#include "openfhe.h"
#include "proofsystem/proofsystem_libsnark.h"
#include <vector>
#include <cassert>

using namespace lbcrypto;
using std::cout, std::endl;
using std::vector;

std::default_random_engine generator(std::hash<std::string>()("sok-logistic-regression-inference-nonbatched"));

void fill_pseudorandom(vector<int64_t>& vec, int64_t min, int64_t max) {
    std::uniform_int_distribution<int64_t> distribution(min, max);
    std::generate(vec.begin(), vec.end(), [&distribution]() { return distribution(generator); });
}

void fill_pseudorandom_nonzero(vector<int64_t>& vec, int64_t min, int64_t max) {
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
    // Application setup
    const size_t max_feature_value = 100;
    const size_t num_features      = 8;
    const size_t log_num_features  = ceil(log2(num_features));
    vector<int> rotation_indices;
    for (size_t i = 0; i < log_num_features; i++) {
        rotation_indices.push_back(1 << i);
    }
    const size_t approximation_degree     = 2;
    const size_t log_approximation_degree = ceil(log2(approximation_degree));

    // FHE Setup
    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetSecurityLevel(SecurityLevel::HEStd_NotSet);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    parameters.SetKeySwitchTechnique(BV);
    parameters.SetRingDim(2048);
    parameters.SetMultiplicativeDepth(2);

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
    vector<int64_t> vec(1);

    vector<Ciphertext<DCRTPoly>> client_in_1, client_in_2;
    for (size_t i = 0; i < num_features; ++i) {
        fill_pseudorandom(vec, 0, max_feature_value);
        client_in_1.push_back(cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(vec)));
        fill_pseudorandom(vec, 0, max_feature_value);
        client_in_2.push_back(cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(vec)));
    }

    // Server.Eval
    // Product
    vector<Ciphertext<DCRTPoly>> prod(num_features);
    vector<Ciphertext<DCRTPoly>> aggs(num_features);
    for (size_t i = 0; i < num_features; ++i) {
        prod[i] = cryptoContext->EvalMultNoRelin(client_in_1[i], client_in_2[i]);
        aggs[i] = (i == 0) ? prod[i] : cryptoContext->EvalAdd(aggs[i - 1], prod[i]);
    }
    //    auto relined = cryptoContext->Relinearize(prod);
    cout << "prod := client_in * server_in" << endl;

    // Apply sigmoid approximation
    Ciphertext<DCRTPoly> sum = aggs[num_features - 1];
    auto out                 = cryptoContext->EvalMultNoRelin(sum, sum);

    // Client.Decrypt
    Plaintext result;
    cryptoContext->Decrypt(keyPair.secretKey, out, &result);

    // Do it all again with the ZKP
    LibsnarkProofSystem ps(cryptoContext);
    for (size_t i = 0; i < num_features; ++i) {
        ps.ConstrainPublicInput(client_in_1[i]);
        ps.ConstrainPublicInput(client_in_2[i]);
    }
    auto vars_out = *ps.ConstrainPublicOutput(out);

    // Product
    //    auto prod = cryptoContext->EvalMult(client_in, server_in);
    for (size_t i = 0; i < num_features; ++i) {
        ps.ConstrainMultiplication(client_in_1[i], client_in_2[i], prod[i]);
        if (i > 0) {
            ps.ConstrainAddition(aggs[i - 1], prod[i], aggs[i]);
        }
    }
    cout << "prod := client_in * server_in" << endl;
    print(ps);

    ps.ConstrainSquare2(sum, out);
    print(ps);

    cout
        << "== Done with main circuit, finalizing output constraints and eagerly mod-reducing outstanding constraints ==="
        << endl;
    ps.FinalizeOutputConstraints(out, vars_out);

    cout << "==============" << endl;
    print(ps);
    std::cout << std::flush;

    return 0;
}
