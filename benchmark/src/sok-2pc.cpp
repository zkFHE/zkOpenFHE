#include "scheme/ckksrns/cryptocontext-ckksrns.h"
#include "gen-cryptocontext.h"
#include "nn-helper.h"

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

std::default_random_engine generator(std::hash<std::string>()(("sok-nn")));

class CustomFixture : public benchmark::Fixture {
public:
    // Crypto values
    CryptoContext<DCRTPoly> cryptoContext;
    KeyPair<DCRTPoly> keyPair;

    // Application-specific constants
    /// Size of the input vector, i.e. flattened 32x32 image
    const size_t input_size = 1024;  // 32x32
    vector<int> rotation_indices;

    // We pad the MNIST images from 28x28 to 32x32
    // because of fast MVP we use requires that the input size divides # of units in the dense layers
    // and the result must be a power of two
    /// vectorized (padded) MNIST image
    std::vector<double> image = random_vector(input_size, generator);

    // Inputs and outputs
    DenseLayer d1, d2;
    Ciphertext<DCRTPoly> image_ctxt, mv_1, mvb_1, mvb_1_rescaled, h1_sq, h1_sq_relin, h1_sq_rescaled, masked, tmp,
        tmp_agg, in2, mv_2, mvb_2, out;

    r1cs_constraint_system<FieldT>* constraint_system;

    r1cs_gg_ppzksnark_verification_key<ppT>* verification_key;
    r1cs_gg_ppzksnark_proof<ppT>* proof;
    r1cs_primary_input<FieldT>* primary_input;

    CustomFixture() {
        libff::default_ec_pp::init_public_params();
        libff::inhibit_profiling_info     = true;
        libff::inhibit_profiling_counters = true;
    }

    void eval() {
        // First, compute the MVP between d1_weights and the input
        ptxt_general_matrix_enc_vector_product(cryptoContext, d1.units(), d1.input_size(), d1.weights_as_diags(),
                                               image_ctxt, mv_1);

        // Now add the bias
        Plaintext b1 = cryptoContext->MakeCKKSPackedPlaintext(d1.bias());
        mvb_1        = cryptoContext->EvalAdd(mv_1, b1);

        // Rescale, since MVP does not rescale internally
        mvb_1_rescaled = cryptoContext->Rescale(mvb_1);

        // Activation, x -> x^2
        h1_sq          = cryptoContext->EvalMult(mvb_1_rescaled, mvb_1_rescaled);
        h1_sq_relin    = cryptoContext->Relinearize(h1_sq);
        h1_sq_rescaled = cryptoContext->Rescale(h1_sq_relin);

        // In order to fulfill the requirements for a "well rotatable" input vector, we must "duplicate" homomorphically
        Plaintext mask = cryptoContext->MakeCKKSPackedPlaintext(vec(1, d1.units()));
        masked         = cryptoContext->EvalMult(h1_sq_rescaled, mask);
        tmp            = cryptoContext->EvalRotate(masked, d1.units());
        tmp_agg        = cryptoContext->EvalAdd(tmp, masked);
        in2            = cryptoContext->Rescale(tmp_agg);

        // Weights
        ptxt_general_matrix_enc_vector_product(cryptoContext, d2.units(), d2.input_size(), d2.weights_as_diags(), in2,
                                               mv_2);

        // Bias
        Plaintext b2 = cryptoContext->MakeCKKSPackedPlaintext(d2.bias());
        mvb_2        = cryptoContext->EvalAdd(mv_2, b2);

        // Rescale, since MVP does not rescale internally
        out = cryptoContext->Rescale(mvb_2);
    }

    void SetUp(const ::benchmark::State& state) {
        CCParams<CryptoContextCKKSRNS> parameters;
        parameters.SetSecurityLevel(SecurityLevel::HEStd_128_classic);
        parameters.SetMultiplicativeDepth(5);
        parameters.SetScalingTechnique(FIXEDMANUAL);
        parameters.SetKeySwitchTechnique(BV);
        parameters.SetFirstModSize(60);
        parameters.SetScalingModSize(40);
        parameters.SetMaxRelinSkDeg(1);
        parameters.SetDigitSize(0);

        cryptoContext = GenCryptoContext(parameters);
        cryptoContext->Enable(PKE);
        cryptoContext->Enable(KEYSWITCH);
        cryptoContext->Enable(LEVELEDSHE);

        d1 = DenseLayer(32, input_size, generator);

        // Create the Weights and Biases for the second  dense layer
        // We use 16, even though MNIST has osssssnly 10 classes, because of the power-of-two requirement
        // The model should have the weights for those 6 "dummy classes" forced to zero and the client can simply ignore them
        d2 = DenseLayer(16, d1.units(), generator);

        rotation_indices = custom_steps(1024);
        // TODO: we need to generate keys for rotations of {1, ..., d1.units()}
        for (int i = 1; i < 32; i++) {
            rotation_indices.push_back(i);
        }

        // Server.Keygen
        keyPair = cryptoContext->KeyGen();
        cryptoContext->EvalMultKeyGen(keyPair.secretKey);
        cryptoContext->EvalRotateKeyGen(keyPair.secretKey, rotation_indices);
        // Client.Encode, Client.Encrypt_pk
        image_ctxt = cryptoContext->Encrypt(keyPair.publicKey, cryptoContext->MakeCKKSPackedPlaintext(image));

        // Server.Encode, Server.Encrypt_sk
        eval();
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

BENCHMARK_F(CustomFixture, Outsourcing_FHE_Server_Eval)(benchmark::State& state) {
    // BENCH: eval
    for (auto _ : state) {
        eval();
    }
}

BENCHMARK_F(CustomFixture, Outsourcing_FHE_Client_Eval)(benchmark::State& state) {
    // BENCH: (single) encryption + (single) decryption
    Plaintext result;
    for (auto _ : state) {
        auto image_ctxt = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakeCKKSPackedPlaintext(image));
                cryptoContext->Decrypt(keyPair.secretKey, out, &result); // TODO: add a workaround to make sure this decryption is successful
    }
}

BENCHMARK_MAIN();
