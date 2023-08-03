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

std::default_random_engine generator(std::hash<std::string>()(("sok-tracing-protect")));

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

    Plaintext one;

    usint ptm              = 65537;
    usint depth            = 3;
    const int max_position = 100;

    vector<int64_t> client_pos_i_vec, client_pos_j_vec, client_random_blinding_vec, server_pos_i_vec, server_pos_j_vec,
        zero_vec;
    Plaintext client_pos_i, client_pos_j, client_random_blinding, zero;
    Ciphertext<DCRTPoly> server_pos_i, server_pos_j, d_i, d_j, d_i_min_d_j, d_i_min_d_j_squared, d_i_mul_d_j, c_dist,
        c_dist_relin, c_dist_squared_min_one, c_prox, c_out_blinded, output;

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
        CCParams<CryptoContextBGVRNS> parameters;
        parameters.SetPlaintextModulus(ptm);
        parameters.SetMultiplicativeDepth(depth);
        parameters.SetKeySwitchTechnique(BV);
        parameters.SetScalingTechnique(FIXEDMANUAL);

        cryptoContext = GenCryptoContext(parameters);
        cryptoContext->Enable(PKE);
        cryptoContext->Enable(KEYSWITCH);
        cryptoContext->Enable(LEVELEDSHE);

        keyPair = cryptoContext->KeyGen();
        cryptoContext->EvalMultKeyGen(keyPair.secretKey);

        // Initialize message vectors
        auto N = cryptoContext->GetRingDimension();
        fill_pseudorandom(client_pos_i_vec, N, 0, max_position);
        fill_pseudorandom(client_pos_j_vec, N, 0, max_position);
        fill_pseudorandom_nonzero(client_random_blinding_vec, N, LowBound(cryptoContext->GetEncodingParams()),
                                  HighBound(cryptoContext->GetEncodingParams()));
        fill_pseudorandom(server_pos_i_vec, N, 0, max_position);
        fill_pseudorandom(server_pos_j_vec, N, 0, max_position);
        zero_vec = vector<int64_t>(N, 0);

        // Initialize public constants
        one = cryptoContext->MakePackedPlaintext(vector<int64_t>(cryptoContext->GetRingDimension(), 1));

        // Initialize output ciphertext to decrypt

        // Client.Encode, Client.Encrypt_pk
        assert(client_pos_i_vec.size() == cryptoContext->GetRingDimension());
        client_pos_i           = cryptoContext->MakePackedPlaintext(client_pos_i_vec);
        client_pos_j           = cryptoContext->MakePackedPlaintext(client_pos_j_vec);
        client_random_blinding = cryptoContext->MakePackedPlaintext(client_random_blinding_vec);
        //         client_noiseflooding_0 =
        //            cryptoContext->Encrypt(keyPair.publicKey, cryptoContext->MakePackedPlaintext(zero_vec));

        // Server.Encode, Server.Encrypt_pk
        server_pos_i = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(server_pos_i_vec));
        server_pos_j = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(server_pos_j_vec));

        // Client.Eval
        d_i = cryptoContext->EvalSub(server_pos_i, client_pos_i);
        d_j = cryptoContext->EvalSub(server_pos_i, client_pos_j);

        d_i_min_d_j = cryptoContext->EvalSub(d_i, d_j);
        //        d_i_min_d_j_squared = cryptoContext->EvalSquare(d_i_min_d_j);
        d_i_min_d_j_squared = cryptoContext->EvalMultNoRelin(d_i_min_d_j, d_i_min_d_j);
        d_i_mul_d_j         = cryptoContext->EvalMultNoRelin(d_i, d_j);

        c_dist = cryptoContext->EvalAdd(d_i_min_d_j_squared, d_i_mul_d_j);
        // TODO: unclear of where relinearization should happen from the description in the PROTECT paper
        c_dist_relin = cryptoContext->Relinearize(c_dist);

        c_dist_squared_min_one = cryptoContext->EvalSub(c_dist_relin, one);
        c_prox                 = cryptoContext->EvalMult(c_dist_relin, c_dist_squared_min_one);

        c_out_blinded = cryptoContext->EvalMult(c_prox, client_random_blinding);
        output        = c_out_blinded;  //cryptoContext->EvalAdd(c_out_blinded, client_noiseflooding_0);

        // Initialize proof system

        /*  // Server.Encode, Server.Encrypt_pk
        LibsnarkProofSystem ps(cryptoContext);

        ps.ConstrainPublicInput(server_pos_i);
        ps.ConstrainPublicInput(server_pos_j);

        // Client.Eval
        //        auto d_i = cryptoContext->EvalSub(client_pos_i, server_pos_i);
        //        auto d_j = cryptoContext->EvalSub(client_pos_j, server_pos_j);
        ps.ConstrainSubstraction(server_pos_i, client_pos_i, d_i);
        ps.ConstrainSubstraction(server_pos_j, client_pos_j, d_j);

        //        auto d_i_min_d_j         = cryptoContext->EvalSub(d_i, d_j);
        ps.ConstrainSubstraction(d_i, d_j, d_i_min_d_j);
        //        auto d_i_min_d_j_squared = cryptoContext->EvalSquare(d_i_min_d_j);
        ps.ConstrainSquare(d_i_min_d_j, d_i_min_d_j_squared);
        //        auto d_i_mul_d_j         = cryptoContext->EvalMult(d_i, d_j);
        ps.ConstrainMultiplication(d_i, d_j, d_i_mul_d_j);

        //        auto c_dist = cryptoContext->EvalAdd(d_i_min_d_j_squared, d_i_mul_d_j);
        ps.ConstrainAddition(d_i_min_d_j_squared, d_i_mul_d_j, c_dist);
        // Unclear of where relinearization should happen from the description in the PROTECT paper, we put it here as it makes the most sense
        //        auto c_dist_relin = cryptoContext->Relinearize(c_dist);
        ps.ConstrainRelin(c_dist, c_dist_relin);

        //        auto c_dist_squared_min_one = cryptoContext->EvalSub(c_dist_relin, one);
        ps.ConstrainSubstraction(c_dist_relin, one, c_dist_squared_min_one);
        //        auto c_prox                 = cryptoContext->EvalMult(c_dist, c_dist_squared_min_one);
        ps.ConstrainMultiplication(c_dist_relin, c_dist_squared_min_one, c_prox);

        //        auto c_out_blinded = cryptoContext->EvalMult(c_prox, client_random_blinding);
        ps.ConstrainMultiplication(c_prox, client_random_blinding, c_out_blinded);
        //        output = cryptoContext->EvalAdd(c_out_blinded, client_noiseflooding_0);
        ps.ConstrainMultiplication(c_out_blinded, client_noiseflooding_0, output);

        // Initialize verifier and (dummy) proof
        {
            protoboard<FieldT> pb;
            pb_variable<FieldT> v1, v2;
            v1.allocate(pb, "v1");
            v2.allocate(pb, "v2");
            pb.add_r1cs_constraint(r1cs_constraint<FieldT>(v1, v2, v1));

            pb.set_input_sizes(1);
            r1cs_gg_ppzksnark_keypair<ppT> keypair = r1cs_gg_ppzksnark_generator<ppT>(pb.get_constraint_system());

            pb.val(v1)       = FieldT::one();
            pb.val(v2)       = FieldT::one();
            primary_input    = new r1cs_primary_input<FieldT>(pb.primary_input());
            verification_key = new r1cs_gg_ppzksnark_verification_key<ppT>(keypair.vk);
            auto pi          = r1cs_gg_ppzksnark_prover(keypair.pk, pb.primary_input(), pb.auxiliary_input());
            proof            = new r1cs_gg_ppzksnark_proof(pi);
            //            const bool b = r1cs_gg_ppzksnark_verifier_strong_IC<default_r1cs_gg_ppzksnark_pp>(*verification_key, *primary_input,
            //                                                                                *proof);
            //            assert(b);
        }
        */
    }
};

BENCHMARK_F(CustomFixture, Flipped2PC_Server_FHE_Setup)(benchmark::State& state) {
    for (auto _ : state) {
        // Server.Keygen
        KeyPair<DCRTPoly> keyPair = cryptoContext->KeyGen();
        cryptoContext->EvalMultKeyGen(keyPair.secretKey);
    }
}

BENCHMARK_F(CustomFixture, Flipped2PC_Server_FHE_Eval)(benchmark::State& state) {
    for (auto _ : state) {
        // Server.Encode, Server.Encrypt_sk
        auto server_pos_i =
            cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(server_pos_i_vec));
        auto server_pos_j =
            cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(server_pos_j_vec));
        // Server.Decode
        Plaintext result;
        cryptoContext->Decrypt(keyPair.secretKey, output, &result);
    }
}

BENCHMARK_F(CustomFixture, Flipped2PC_Client_FHE_Eval)(benchmark::State& state) {
    // BENCH: eval
    for (auto _ : state) {
        d_i = cryptoContext->EvalSub(server_pos_i, client_pos_i);
        d_j = cryptoContext->EvalSub(server_pos_i, client_pos_j);

        d_i_min_d_j = cryptoContext->EvalSub(d_i, d_j);
        //        d_i_min_d_j_squared = cryptoContext->EvalSquare(d_i_min_d_j);
        d_i_min_d_j_squared = cryptoContext->EvalMultNoRelin(d_i_min_d_j, d_i_min_d_j);
        d_i_mul_d_j         = cryptoContext->EvalMultNoRelin(d_i, d_j);

        c_dist = cryptoContext->EvalAdd(d_i_min_d_j_squared, d_i_mul_d_j);
        // TODO: unclear of where relinearization should happen from the description in the PROTECT paper
        c_dist_relin = cryptoContext->Relinearize(c_dist);

        c_dist_squared_min_one = cryptoContext->EvalSub(c_dist_relin, one);
        c_prox                 = cryptoContext->EvalMult(c_dist_relin, c_dist_squared_min_one);

        c_out_blinded = cryptoContext->EvalMult(c_prox, client_random_blinding);
        output        = c_out_blinded;  //cryptoContext->EvalAdd(c_out_blinded, client_noiseflooding_0);
    }
}

/*
BENCHMARK_F(CustomFixture, Flipped2PC_ZKP)(benchmark::State& state) {
    for (auto _ : state) {
        LibsnarkProofSystem ps(cryptoContext);

        ps.ConstrainPublicInput(server_pos_i);
        ps.ConstrainPublicInput(server_pos_j);
        auto vars_out = ps.ConstrainPublicOutput(output);

        // Client.Eval
        //        auto d_i = cryptoContext->EvalSub(client_pos_i, server_pos_i);
        //        auto d_j = cryptoContext->EvalSub(client_pos_j, server_pos_j);
        ps.ConstrainSubstraction(server_pos_i, client_pos_i, d_i);
        ps.ConstrainSubstraction(server_pos_j, client_pos_j, d_j);

        //        auto d_i_min_d_j         = cryptoContext->EvalSub(d_i, d_j);
        ps.ConstrainSubstraction(d_i, d_j, d_i_min_d_j);
        //        auto d_i_min_d_j_squared = cryptoContext->EvalSquare(d_i_min_d_j);
        ps.ConstrainMultiplication(d_i_min_d_j, d_i_min_d_j, d_i_min_d_j_squared);
        //        auto d_i_mul_d_j         = cryptoContext->EvalMult(d_i, d_j);
        ps.ConstrainMultiplication(d_i, d_j, d_i_mul_d_j);

        //        auto c_dist = cryptoContext->EvalAdd(d_i_min_d_j_squared, d_i_mul_d_j);
        ps.ConstrainAddition(d_i_min_d_j_squared, d_i_mul_d_j, c_dist);
        // Unclear of where relinearization should happen from the description in the PROTECT paper, we put it here as it makes the most sense
        //        auto c_dist_relin = cryptoContext->Relinearize(c_dist);
        ps.ConstrainRelin(c_dist, c_dist_relin);

        //        auto c_dist_squared_min_one = cryptoContext->EvalSub(c_dist_relin, one);
        ps.ConstrainSubstraction(c_dist_relin, one, c_dist_squared_min_one);
        //        auto c_prox                 = cryptoContext->EvalMult(c_dist, c_dist_squared_min_one);
        ps.ConstrainMultiplication(c_dist_relin, c_dist_squared_min_one, c_prox);

        //        auto c_out_blinded = cryptoContext->EvalMult(c_prox, client_random_blinding);
        ps.ConstrainMultiplication(c_prox, client_random_blinding, c_out_blinded);
        //        output = cryptoContext->EvalAdd(c_out_blinded, client_noiseflooding_0);
        //    ps.ConstrainMultiplication(c_out_blinded, client_noiseflooding_0, output);

        ps.FinalizeOutputConstraints(output, *vars_out);

        auto pb = ps.pb;
        cout << "#inputs:      " << pb.num_inputs() << endl;
        cout << "#variables:  " << pb.num_variables() << endl;
        cout << "#constraints: " << pb.num_constraints() << endl;
    }
}
*/

BENCHMARK_MAIN();
