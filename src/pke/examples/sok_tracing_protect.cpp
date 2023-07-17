/*
  Implementation of the [PROTECT protocol](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC8276784/), as used in the Korean COVID-19 tracing app Cordong-I.
  We follow the description of the protocol exactly, but we use BGV instead of B/FV, and we allow ourselves to tweak the ring dimension N (8192 in the paper), as well as the plaintext modulus (unspecified in the paper).
 */

#include "openfhe.h"
#include <vector>
#include <cassert>

using namespace lbcrypto;
using std::cout, std::endl;
using std::vector;

std::default_random_engine generator(std::hash<std::string>()(("sok_tracing_protect")));

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
    const size_t max_position = 100;

    // FHE Setup
    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetSecurityLevel(SecurityLevel::HEStd_128_classic);
    parameters.SetMultiplicativeDepth(3);
    parameters.SetPlaintextModulus(65537);

    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);
    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);
    const Plaintext one = cryptoContext->MakePackedPlaintext(vector<int64_t>(cryptoContext->GetRingDimension(), 1));

    // Server.Keygen
    KeyPair<DCRTPoly> keyPair = cryptoContext->KeyGen();
    cryptoContext->EvalMultKeyGen(keyPair.secretKey);

    // Client.Encode, Client.Encrypt_pk
    vector<int64_t> vec(cryptoContext->GetRingDimension());

    fill_pseudorandom(vec, 0, max_position);
    Plaintext client_pos_i = cryptoContext->MakePackedPlaintext(vec);

    fill_pseudorandom(vec, 0, max_position);
    Plaintext client_pos_j = cryptoContext->MakePackedPlaintext(vec);

    // Sample from Z_t \ {0}
    fill_pseudorandom_nonzero(vec, LowBound(cryptoContext->GetEncodingParams()),
                              HighBound(cryptoContext->GetEncodingParams()));
    Plaintext client_random_blinding = cryptoContext->MakePackedPlaintext(vec);

    std::fill(vec.begin(), vec.end(), 0);
    auto client_noiseflooding_0 = cryptoContext->Encrypt(keyPair.publicKey, cryptoContext->MakePackedPlaintext(vec));

    // Server.Encode, Server.Encrypt_sk
    fill_pseudorandom(vec, 0, max_position);
    auto server_pos_i = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(vec));

    fill_pseudorandom(vec, 0, max_position);
    auto server_pos_j = cryptoContext->Encrypt(keyPair.secretKey, cryptoContext->MakePackedPlaintext(vec));

    // Client.Eval
    auto d_i = cryptoContext->EvalSub(client_pos_i, server_pos_i);
    auto d_j = cryptoContext->EvalSub(client_pos_j, server_pos_j);

    auto d_i_min_d_j         = cryptoContext->EvalSub(d_i, d_j);
    auto d_i_min_d_j_squared = cryptoContext->EvalSquare(d_i_min_d_j);
    auto d_i_mul_d_j         = cryptoContext->EvalMult(d_i, d_j);

    auto c_dist = cryptoContext->EvalAdd(d_i_min_d_j_squared, d_i_mul_d_j);
    // TODO: unclear of where relinearization should happen from the description in the PROTECT paper
    c_dist = cryptoContext->Relinearize(c_dist);

    auto c_dist_squared_min_one = cryptoContext->EvalSub(c_dist, one);
    auto c_prox                 = cryptoContext->EvalMult(c_dist, c_dist_squared_min_one);

    auto c_out_blinded = cryptoContext->EvalMult(c_prox, client_random_blinding);
    auto c_out         = cryptoContext->EvalAdd(c_out_blinded, client_noiseflooding_0);

    // Server.Decrypt
    Plaintext result;
    cryptoContext->Decrypt(keyPair.secretKey, c_out, &result);

    // Application checks
    size_t num_contacts = 0;
    auto matches        = result->GetPackedValue();
    for (size_t timestamp = 0; timestamp < matches.size(); timestamp++) {
        if (matches[timestamp] == 0) {
            num_contacts++;
            cout << "Contact at timestamp " << timestamp << endl;
        }
    }
    cout << "Number of contacts: " << num_contacts << endl;

    return 0;
}
