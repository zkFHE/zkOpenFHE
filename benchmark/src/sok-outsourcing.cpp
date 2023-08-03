#include "scheme/bgvrns/cryptocontext-bgvrns.h"
#include "gen-cryptocontext.h"

#include "proofsystem/proofsystem_libsnark.h"
#include "proofsystem/proofsystem_libsnark.cpp"  // TODO FIXME

#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

#include "benchmark/benchmark.h"

#include <iostream>
#include <fstream>
#include <limits>
#include <iterator>
#include <random>
#include <cassert>

using std::cout, std::endl;
using namespace lbcrypto;
using namespace libsnark;
using ppT = default_r1cs_ppzksnark_pp;
typedef libff::Fr<ppT> FieldT;

std::default_random_engine generator(std::hash<std::string>()(("sok-logistic-regression")));

void fill_pseudorandom(vector<int64_t>& vec, size_t length, int64_t min, int64_t max) {
    vec.resize(length);
    std::uniform_int_distribution<int64_t> distribution(min, max);
    std::generate(vec.begin(), vec.end(), [&distribution]() { return distribution(generator); });
}

void fill_pseudorandom_nonzero(vector<int64_t>& vec, size_t length, int64_t min, int64_t max) {
    vec.resize(length);
    std::uniform_int_distribution<int64_t> distribution(min, max);
    std::generate(vec.begin(), vec.end(), [&distribution]() {
        int64_t res;
        do {
            res = distribution(generator);
        } while (res == 0);
        return res;
    });
}

// From src/pke/include/encoding/plaintext.h
/**
   * Calculate and return lower bound that can be encoded with the plaintext
   * modulus the number to encode MUST be greater than this value
   * @return floor(-p/2)
   */
int64_t LowBound(const EncodingParams& encodingParams) {
    uint64_t half = encodingParams->GetPlaintextModulus() >> 1;
    bool odd      = (encodingParams->GetPlaintextModulus() & 0x1) == 1;
    int64_t bound = -1 * half;
    if (odd)
        bound--;
    return bound;
}

// From src/pke/include/encoding/plaintext.h
/**
   * Calculate and return upper bound that can be encoded with the plaintext
   * modulus the number to encode MUST be less than or equal to this value
   * @return floor(p/2)
   */
int64_t HighBound(const EncodingParams& encodingParams) {
    return encodingParams->GetPlaintextModulus() >> 1;
}

class CustomFixture : public benchmark::Fixture {
public:
    CryptoContext<DCRTPoly> cryptoContext;
    KeyPair<DCRTPoly> keyPair;

    const size_t max_feature_value = 100;
    const size_t num_features      = 512;
    const size_t log_num_features  = ceil(log2(num_features));
    vector<int> rotation_indices;

    const size_t approximation_degree     = 8;
    const size_t log_approximation_degree = ceil(log2(approximation_degree));

    vector<int64_t> client_in_vec_1, client_in_vec_2;
    Plaintext client_in_ptxt_1, client_in_ptxt_2;
    Ciphertext<DCRTPoly> client_in_1, client_in_2;
    vector<Ciphertext<DCRTPoly>> rots, aggs, pows, sigs;
    Ciphertext<DCRTPoly> out;

    r1cs_constraint_system<FieldT>* constraint_system;

    r1cs_gg_ppzksnark_verification_key<ppT>* verification_key;
    r1cs_gg_ppzksnark_proof<ppT>* proof;
    r1cs_primary_input<FieldT>* primary_input;

    CustomFixture() {
        libff::default_ec_pp::init_public_params();
        libff::inhibit_profiling_info     = true;
        libff::inhibit_profiling_counters = true;
    }

    void SetUp(const ::benchmark::State& state) {
        // TODO: initialize all values only once using global/static variables

        // Application setup
        for (int i = 0; i < log_num_features; i++) {
            rotation_indices.push_back(1 << i);
        }

        // FHE Setup
        CCParams<CryptoContextBGVRNS> parameters;
        parameters.SetSecurityLevel(SecurityLevel::HEStd_128_classic);
        parameters.SetMultiplicativeDepth(log_approximation_degree);
        parameters.SetPlaintextModulus(4295294977);  // 32 bit, to be compatible with Lattigo example
        parameters.SetScalingTechnique(FIXEDMANUAL);
        parameters.SetKeySwitchTechnique(BV);

        CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);
        cryptoContext->Enable(PKE);
        cryptoContext->Enable(KEYSWITCH);
        cryptoContext->Enable(LEVELEDSHE);

        cout << "N =    " << cryptoContext->GetRingDimension() << endl;
        cout << "logT = " << GetMSB(parameters.GetPlaintextModulus()) << endl;

        // Server.Keygen
        KeyPair<DCRTPoly> keyPair = cryptoContext->KeyGen();
        cryptoContext->EvalMultKeyGen(keyPair.secretKey);
        cryptoContext->EvalRotateKeyGen(keyPair.secretKey, rotation_indices);

        // Client.Encode, Client.Encrypt_pk
        fill_pseudorandom(client_in_vec_1, num_features, 0, max_feature_value);
        client_in_ptxt_1 = cryptoContext->MakePackedPlaintext(client_in_vec_1);
        client_in_1      = cryptoContext->Encrypt(keyPair.secretKey, client_in_ptxt_1);
        fill_pseudorandom(client_in_vec_2, num_features, 0, max_feature_value);
        client_in_ptxt_2 = cryptoContext->MakePackedPlaintext(client_in_vec_2);
        client_in_2      = cryptoContext->Encrypt(keyPair.secretKey, client_in_ptxt_2);

        // Server.Eval
        // Product
        auto prod    = cryptoContext->EvalMultNoRelin(client_in_1, client_in_2);
        auto relined = cryptoContext->Relinearize(prod);
        cout << "prod := client_in * server_in" << endl;

        // Aggregate to get inner product
        rots = vector<Ciphertext<DCRTPoly>>(1 + log_num_features);  // rots[i] == rotate(rots[i-1], 2^i), rots[0] = prod
        aggs = vector<Ciphertext<DCRTPoly>>(1 + log_num_features);  // aggs[i] == rots[i-1] + rots[i]
        rots[0] = relined;
        aggs[0] = relined;
        cout << "num_features = " << num_features << " = 2^" << log_num_features << endl;
        for (size_t i = 1; i < log_num_features; i++) {
            int rot_amt = 1 << (i - 1);
            rots[i]     = cryptoContext->EvalRotate(aggs[i - 1], rot_amt);
            aggs[i]     = cryptoContext->EvalAdd(aggs[i - 1], rots[i]);
            cout << "ag_" << i << " := rot(prod, 2^" << i << ") + ag_" << i - 1 << endl;
        }

        // Apply sigmoid approximation
        pows    = vector<Ciphertext<DCRTPoly>>(1 + log_approximation_degree);
        sigs    = vector<Ciphertext<DCRTPoly>>(1 + log_approximation_degree);
        pows[0] = aggs[log_num_features - 1];
        sigs[0] = pows[0];
        cout << "approximation_degree = " << approximation_degree << " = 2^" << log_approximation_degree << endl;
        for (size_t i = 1; i <= log_approximation_degree; i++) {
            pows[i] = cryptoContext->EvalMultNoRelin(sigs[i - 1], sigs[i - 1]);
            sigs[i] = cryptoContext->Relinearize(pows[i]);
            cout << "sg_" << i << " := relin(sg_" << i - 1 << "^2)" << endl;
        }
        out = sigs[log_approximation_degree];

        // Client.Decrypt
        Plaintext result;
        cryptoContext->Decrypt(keyPair.secretKey, out, &result);
    }
};

BENCHMARK_F(CustomFixture, Outsourcing_FHE_Client_Setup)(benchmark::State& state) {
    // BENCH: keygen
    for (auto _ : state) {
        // Server.Keygen
        KeyPair<DCRTPoly> keyPair = cryptoContext->KeyGen();
        cryptoContext->EvalMultKeyGen(keyPair.secretKey);
        cryptoContext->EvalRotateKeyGen(keyPair.secretKey, rotation_indices);
    }
}

BENCHMARK_F(CustomFixture, Outsourcing_FHE_Client_Eval)(benchmark::State& state) {
    // BENCH: (single) encryption + (single) decryption
    Plaintext result;
    for (auto _ : state) {
        auto client_in_1 =
            cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(client_in_vec_1));
        auto client_in_2 =
            cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(client_in_vec_2));
        cryptoContext->Decrypt(keyPair.secretKey, out, &result);
    }
}

BENCHMARK_F(CustomFixture, Outsourcing_FHE_Server_Eval)(benchmark::State& state) {
    // BENCH: eval
    for (auto _ : state) {
        auto prod    = cryptoContext->EvalMultNoRelin(client_in_1, client_in_2);
        auto relined = cryptoContext->Relinearize(prod);

        // Aggregate to get inner product
        rots = vector<Ciphertext<DCRTPoly>>(1 + log_num_features);  // rots[i] == rotate(rots[i-1], 2^i), rots[0] = prod
        aggs = vector<Ciphertext<DCRTPoly>>(1 + log_num_features);  // aggs[i] == rots[i-1] + rots[i]
        rots[0] = relined;
        aggs[0] = relined;
        for (size_t i = 1; i < log_num_features; i++) {
            int rot_amt = 1 << (i - 1);
            rots[i]     = cryptoContext->EvalRotate(aggs[i - 1], rot_amt);
            aggs[i]     = cryptoContext->EvalAdd(aggs[i - 1], rots[i]);
        }

        // Apply sigmoid approximation
        pows    = vector<Ciphertext<DCRTPoly>>(1 + log_approximation_degree);
        sigs    = vector<Ciphertext<DCRTPoly>>(1 + log_approximation_degree);
        pows[0] = aggs[log_num_features - 1];
        sigs[0] = pows[0];
        for (size_t i = 1; i <= log_approximation_degree; i++) {
            pows[i] = cryptoContext->EvalMultNoRelin(sigs[i - 1], sigs[i - 1]);
            sigs[i] = cryptoContext->Relinearize(pows[i]);
        }
        out = sigs[log_approximation_degree];
    }
}

BENCHMARK_MAIN();
