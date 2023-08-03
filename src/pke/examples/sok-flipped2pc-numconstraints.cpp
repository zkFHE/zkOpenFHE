#include "scheme/bgvrns/cryptocontext-bgvrns.h"
#include "gen-cryptocontext.h"

#include "proofsystem/proofsystem_libsnark.h"
#include "proofsystem/proofsystem_libsnark.cpp"  // TODO FIXME

#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

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

inline void print(const LibsnarkProofSystem& ps) {
    auto pb = ps.pb;
    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#variables:  " << pb.num_variables() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
    cout << endl;
}

int main() {
    libff::default_ec_pp::init_public_params();
    libff::inhibit_profiling_info     = true;
    libff::inhibit_profiling_counters = true;

    CryptoContext<DCRTPoly> cryptoContext;
    KeyPair<DCRTPoly> keyPair;

    Plaintext one;

    usint ptm                    = 65537;
    usint depth                  = 3;
    const int max_position       = 100;
    size_t total_num_inputs      = 0;
    size_t total_num_variables   = 0;
    size_t total_num_constraints = 0;

    vector<int64_t> client_pos_i_vec, client_pos_j_vec, client_random_blinding_vec, server_pos_i_vec, server_pos_j_vec,
        zero_vec;
    Plaintext client_pos_i, client_pos_j, client_random_blinding, zero;
    Ciphertext<DCRTPoly> server_pos_i, server_pos_j, d_i, d_j, d_i_min_d_j, d_i_min_d_j_squared, d_i_mul_d_j, c_dist,
        c_dist_relin, c_dist_squared_min_one, c_prox, c_out_blinded, output;

    ///
    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetPlaintextModulus(ptm);
    parameters.SetMultiplicativeDepth(depth);
    parameters.SetKeySwitchTechnique(BV);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    parameters.SetRingDim(1024);
    parameters.SetSecurityLevel(SecurityLevel::HEStd_NotSet);
    cout << "BGV.N=" << parameters.GetRingDim() << endl;
    cout << "BGV.logT=" << GetMSB(parameters.GetPlaintextModulus()) << endl;

    cryptoContext = GenCryptoContext(parameters);
    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);
    //    for (usint i = 0; i < ; i++)
    //        cout << "BGV.logQ[" << i << "]=" << GetMSB(parameters.GetQ(i)) << endl;
    //}

    cout << "BGV.Q=" <<cryptoContext->GetModulus() << endl;

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

    ///

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

    LibsnarkProofSystem ps(cryptoContext);

    ps.ConstrainPublicInput(server_pos_i);
    ps.ConstrainPublicInput(server_pos_j);
    auto vars_out = ps.ConstrainPublicOutput(output);
    print(ps);

    // Client.Eval
    //        auto d_i = cryptoContext->EvalSub(client_pos_i, server_pos_i);
    //        auto d_j = cryptoContext->EvalSub(client_pos_j, server_pos_j);
    ps.ConstrainSubstraction(server_pos_i, client_pos_i, d_i);
    ps.ConstrainSubstraction(server_pos_j, client_pos_j, d_j);
    print(ps);

    //        auto d_i_min_d_j         = cryptoContext->EvalSub(d_i, d_j);
    ps.ConstrainSubstraction(d_i, d_j, d_i_min_d_j);
    //        auto d_i_min_d_j_squared = cryptoContext->EvalSquare(d_i_min_d_j);
    ps.ConstrainMultiplication(d_i_min_d_j, d_i_min_d_j, d_i_min_d_j_squared);
    //        auto d_i_mul_d_j         = cryptoContext->EvalMult(d_i, d_j);
    ps.ConstrainMultiplication(d_i, d_j, d_i_mul_d_j);
    print(ps);

    //        auto c_dist = cryptoContext->EvalAdd(d_i_min_d_j_squared, d_i_mul_d_j);
    ps.ConstrainAddition(d_i_min_d_j_squared, d_i_mul_d_j, c_dist);
    // Unclear of where relinearization should happen from the description in the PROTECT paper, we put it here as it makes the most sense
    //        auto c_dist_relin = cryptoContext->Relinearize(c_dist);
    ps.ConstrainRelin(c_dist, c_dist_relin);
    print(ps);

    //        auto c_dist_squared_min_one = cryptoContext->EvalSub(c_dist_relin, one);
    ps.ConstrainSubstraction(c_dist_relin, one, c_dist_squared_min_one);
    //        auto c_prox                 = cryptoContext->EvalMult(c_dist, c_dist_squared_min_one);
    ps.ConstrainMultiplication(c_dist_relin, c_dist_squared_min_one, c_prox);
    print(ps);

    //        auto c_out_blinded = cryptoContext->EvalMult(c_prox, client_random_blinding);
    ps.ConstrainMultiplication(c_prox, client_random_blinding, c_out_blinded);
    //        output = cryptoContext->EvalAdd(c_out_blinded, client_noiseflooding_0);
    //    ps.ConstrainMultiplication(c_out_blinded, client_noiseflooding_0, output);
    print(ps);

    cout << "== Done with main circuit, finalizing output constraints and eagerly mod-reducing outstanding constraints ===" << endl;
    ps.FinalizeOutputConstraints(output, *vars_out);

    cout << "==============" << endl;
    print(ps);
    std::cout << std::flush;

    return 0;
}
