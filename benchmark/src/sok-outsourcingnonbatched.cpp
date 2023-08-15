#include "scheme/bgvrns/cryptocontext-bgvrns.h"
#include "gen-cryptocontext.h"

#include "proofsystem/proofsystem_libsnark.h"

#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

#include "benchmark/benchmark.h"

#include <iostream>
#include <iterator>
#include <random>

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
    const size_t num_features      = 64;
    const size_t log_num_features  = ceil(log2(num_features));
    vector<int> rotation_indices;

    vector<int64_t> client_in_vec_1, client_in_vec_2;
    vector<Plaintext> client_in_ptxt_1, client_in_ptxt_2;
    vector<Ciphertext<DCRTPoly>> client_in_1, client_in_2;
    vector<Ciphertext<DCRTPoly>> prod, aggs;
    Ciphertext<DCRTPoly> sum, out;

    r1cs_constraint_system<FieldT>* constraint_system;

    r1cs_gg_ppzksnark_verification_key<ppT>* verification_key;
    r1cs_gg_ppzksnark_proof<ppT>* proof;
    r1cs_primary_input<FieldT>* primary_input;

    CustomFixture() {
        libff::default_ec_pp::init_public_params();
        libff::inhibit_profiling_info     = true;
        libff::inhibit_profiling_counters = true;
    }

    void enc() {
        for (size_t i = 0; i < num_features; ++i) {
            client_in_1[i] =
                (cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext({client_in_vec_1[i]})));
            client_in_2[i] =
                (cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext({client_in_vec_2[i]})));
        }
    }

    void dec() {
        Plaintext result;
        cryptoContext->Decrypt(keyPair.secretKey, out, &result);
    }

    void eval() {
        for (size_t i = 0; i < num_features; ++i) {
            prod[i] = cryptoContext->EvalMultNoRelin(client_in_1[i], client_in_2[i]);
            aggs[i] = (i == 0) ? prod[i] : cryptoContext->EvalAdd(aggs[i - 1], prod[i]);
        }
        sum = aggs[num_features - 1];
        out = cryptoContext->EvalMultNoRelin(sum, sum);
    }

    void SetUp(const ::benchmark::State& state) {
        // TODO: initialize all values only once using global/static variables

        // Application setup
        for (int i = 0; i < log_num_features; i++) {
            rotation_indices.push_back(1 << i);
        }

        // FHE Setup
        CCParams<CryptoContextBGVRNS> parameters;
        parameters.SetSecurityLevel(SecurityLevel::HEStd_NotSet);
        parameters.SetMultiplicativeDepth(2);
        parameters.SetPlaintextModulus(65537);  // 32 bit, to be compatible with Lattigo example
        parameters.SetScalingTechnique(FIXEDMANUAL);
        parameters.SetKeySwitchTechnique(BV);
        parameters.SetRingDim(2048);

        cryptoContext = GenCryptoContext(parameters);
        cryptoContext->Enable(PKE);
        cryptoContext->Enable(KEYSWITCH);
        cryptoContext->Enable(LEVELEDSHE);

        cout << "N =    " << cryptoContext->GetRingDimension() << endl;
        cout << "logT = " << GetMSB(parameters.GetPlaintextModulus()) << endl;

        // Server.Keygen
        keyPair = cryptoContext->KeyGen();
        cryptoContext->EvalMultKeyGen(keyPair.secretKey);
        cryptoContext->EvalRotateKeyGen(keyPair.secretKey, rotation_indices);

        // Client.Encode, Client.Encrypt_pk
        fill_pseudorandom(client_in_vec_1, num_features, 0, max_feature_value);
        fill_pseudorandom(client_in_vec_2, num_features, 0, max_feature_value);

        client_in_1 = vector<Ciphertext<DCRTPoly>>(num_features);
        client_in_2 = vector<Ciphertext<DCRTPoly>>(num_features);
        enc();

        // Server.Eval
        prod = vector<Ciphertext<DCRTPoly>>(num_features);
        aggs = vector<Ciphertext<DCRTPoly>>(num_features);

        eval();

        // Client.Decrypt
        dec();
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
    for (auto _ : state) {
        enc();
        dec();
    }
}

BENCHMARK_F(CustomFixture, Outsourcing_FHE_Server_Eval)(benchmark::State& state) {
    // BENCH: eval
    for (auto _ : state) {
        eval();
    }
}

BENCHMARK_MAIN();
