#include "openfhe.h"
#include <vector>
#include <cassert>

using namespace lbcrypto;
using std::cout, std::endl;
using std::vector;

std::default_random_engine generator(std::hash<std::string>()(("sok-logistic-regression-inference")));

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

int main() {
    // Application setup
    const size_t max_feature_value = 100;
    const size_t num_features      = 512;
    const size_t log_num_features  = ceil(log2(num_features));
    vector<int> rotation_indices;
    for (size_t i = 0; i < log_num_features; i++) {
        rotation_indices.push_back(1 << i);
    }
    const size_t approximation_degree     = 8;
    const size_t log_approximation_degree = ceil(log2(approximation_degree));

    // FHE Setup
    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetSecurityLevel(SecurityLevel::HEStd_128_classic);
    parameters.SetMultiplicativeDepth(log_approximation_degree);
    parameters.SetPlaintextModulus(4295294977);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    parameters.SetKeySwitchTechnique(BV);

    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);
    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    cout << "N =    " << cryptoContext->GetRingDimension() << endl;
    cout << "logT = " << GetMSB(parameters.GetPlaintextModulus()) << endl;

    const Plaintext one = cryptoContext->MakePackedPlaintext(vector<int64_t>(cryptoContext->GetRingDimension(), 1));

    // Server.Keygen
    KeyPair<DCRTPoly> keyPair = cryptoContext->KeyGen();
    cryptoContext->EvalMultKeyGen(keyPair.secretKey);
    cryptoContext->EvalRotateKeyGen(keyPair.secretKey, rotation_indices);

    // Client.Encode, Client.Encrypt_pk
    vector<int64_t> vec(cryptoContext->GetRingDimension());

    fill_pseudorandom(vec, 0, max_feature_value);
    auto client_in_1 = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(vec));
    fill_pseudorandom(vec, 0, max_feature_value);
    auto client_in_2 = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(vec));

    // Server.Eval
    // Product
    auto prod = cryptoContext->EvalMultNoRelin(client_in_1, client_in_2);
    cout << "prod := client_in * server_in" << endl;

    // Aggregate to get inner product
    vector<Ciphertext<DCRTPoly>> rots(1 + log_num_features);  // rots[i] == rotate(rots[i-1], 2^i), rots[0] = prod
    vector<Ciphertext<DCRTPoly>> aggs(1 + log_num_features);  // aggs[i] == rots[i-1] + rots[i]
    rots[0] = prod;
    aggs[0] = prod;
    cout << "num_features = " << num_features << " = 2^" << log_num_features << endl;
    for (size_t i = 1; i < log_num_features; i++) {
        int rot_amt = 1 << (i - 1);
        rots[i]     = cryptoContext->EvalRotate(aggs[i - 1], rot_amt);
        aggs[i]     = cryptoContext->EvalAdd(aggs[i - 1], rots[i]);
        cout << "ag_" << i << " := rot(prod, 2^" << i << ") + ag_" << i - 1 << endl;
    }

    // Apply sigmoid approximation
    vector<Ciphertext<DCRTPoly>> pows(1 + log_approximation_degree);
    vector<Ciphertext<DCRTPoly>> sigs(1 + log_approximation_degree);
    pows[0] = aggs[log_num_features - 1];
    sigs[0] = pows[0];
    cout << "approximation_degree = " << approximation_degree << " = 2^" << log_approximation_degree << endl;
    for (size_t i = 1; i <= log_approximation_degree; i++) {
        pows[i] = cryptoContext->EvalMultNoRelin(sigs[i - 1], sigs[i - 1]);
        sigs[i] = cryptoContext->Relinearize(pows[i]);
        cout << "sg_" << i << " := relin(sg_" << i - 1 << "^2)" << endl;
    }

    // Client.Decrypt
    Plaintext result;
    cryptoContext->Decrypt(keyPair.secretKey, sigs[log_approximation_degree], &result);

    // Application checks
    //    auto out = sigs[log_approximation_degree - 1];
    //    cout << "out: " << out << endl;
    return 0;
}
