/*
Implementation of a 2-layer perceptron for MNIST using CKKS, following the specification in ["SoK: Fully Homomorphic Encryption Compilers"](https://arxiv.org/abs/2101.07078), by Viand et al.
*/

#include "openfhe.h"

#include <vector>
#include <cassert>
#include <stdexcept>
using std::invalid_argument;
using namespace lbcrypto;
using std::cout, std::endl;
using std::vector;

/// Matrix in row-major order
typedef std::vector<std::vector<double>> matrix;

/// Vector
/// Defined to allow clear semantic difference in the code between std::vectors and vectors in the mathematical sense)
typedef std::vector<double> vec;

std::default_random_engine generator(std::hash<std::string>()(("sok-nn-batched")));

// Helper classes
vec random_vector(size_t dim) {
    vec v(dim);
    std::uniform_real_distribution<double> distribution(-0.5, 0.5);
    for (size_t j = 0; j < dim; j++) {
        v[j] = distribution(generator);
    }
    return v;
}

vec add(vec a, vec b) {
    if (a.size() != b.size()) {
        throw invalid_argument("Vectors must have the same dimensions.");
    }
    else {
        vec c(a.size());
        for (size_t i = 0; i < a.size(); i++) {
            c[i] = a[i] + b[i];
        }
        return c;
    }
}

vec mult(vec a, vec b) {
    if (a.size() != b.size()) {
        throw invalid_argument("Vectors must have the same dimensions.");
    }
    else {
        vec c(a.size());
        for (size_t i = 0; i < a.size(); i++) {
            c[i] = a[i] * b[i];
        }
        return c;
    }
}

vec general_mvp_from_diagonals(std::vector<vec> diagonals, vec v) {
    const size_t m = diagonals.size();
    if (m == 0) {
        throw invalid_argument("Matrix must not be empty!");
    }
    const size_t n = diagonals[0].size();
    if (n != v.size() || n == 0) {
        throw invalid_argument("Matrix and vector must have matching non-zero dimension");
    }
    size_t n_div_m      = n / m;
    size_t log2_n_div_m = ceil(log2(n_div_m));
    if (m * n_div_m != n || (2ULL << (log2_n_div_m - 1) != n_div_m && n_div_m != 1)) {
        throw invalid_argument("Matrix dimension m must divide n and the result must be power of two");
    }

    // Hybrid algorithm based on "GAZELLE: A Low Latency Framework for Secure Neural Network Inference" by Juvekar et al.
    // Available at https://www.usenix.org/conference/usenixsecurity18/presentation/juvekar
    // Actual Implementation based on the description in
    // "DArL: Dynamic Parameter Adjustment for LWE-based Secure Inference" by Bian et al. 2019.
    // Available at https://ieeexplore.ieee.org/document/8715110/ (paywall)

    vec t(n, 0);
    for (size_t i = 0; i < m; ++i) {
        vec rotated_v = v;
        rotate(rotated_v.begin(), rotated_v.begin() + i, rotated_v.end());
        auto temp = mult(diagonals[i], rotated_v);
        t         = add(t, temp);
    }

    vec r = t;
    for (int i = 0; i < log2_n_div_m; ++i) {
        vec rotated_r = r;
        size_t offset = n / (2ULL << i);
        rotate(rotated_r.begin(), rotated_r.begin() + offset, rotated_r.end());
        r = add(r, rotated_r);
    }

    r.resize(m);

    return r;
}

void ptxt_general_matrix_enc_vector_product(const CryptoContext<DCRTPoly>& cryptoContext, size_t m, size_t n,
                                            std::vector<vec> diagonals, const Ciphertext<DCRTPoly>& ctv,
                                            Ciphertext<DCRTPoly>& enc_result) {
    if (m == 0 || m != diagonals.size()) {
        throw invalid_argument("Matrix must not be empty, and diagonals vector must have size m!");
    }
    if (n != diagonals[0].size() || n == 0) {
        throw invalid_argument("Diagonals must have non-zero dimension that matches n");
    }
    size_t n_div_m      = n / m;
    size_t log2_n_div_m = ceil(log2(n_div_m));
    if (m * n_div_m != n || (2ULL << (log2_n_div_m - 1) != n_div_m && n_div_m != 1)) {
        throw invalid_argument("Matrix dimension m must divide n and the result must be power of two");
    }

    // Hybrid algorithm based on "GAZELLE: A Low Latency Framework for Secure Neural Network Inference" by Juvekar et al.
    // Available at https://www.usenix.org/conference/usenixsecurity18/presentation/juvekar
    // Actual Implementation based on the description in
    // "DArL: Dynamic Parameter Adjustment for LWE-based Secure Inference" by Bian et al. 2019.
    // Available at https://ieeexplore.ieee.org/document/8715110/ (paywall)

    //  vec t(n, 0);
    Ciphertext<DCRTPoly> ctxt_t;

    for (size_t i = 0; i < m; ++i) {
        // rotated_v = rot(v,i)
        Ciphertext<DCRTPoly> ctxt_rotated_v = ctv;
        if (i != 0) {
            ctxt_rotated_v = cryptoContext->EvalRotate(ctxt_rotated_v, i);
        }

        // auto tmp = mult(diagonals[i], rotated_v);
        Plaintext ptxt_current_diagonal = cryptoContext->MakeCKKSPackedPlaintext(diagonals[i]);
        Ciphertext<DCRTPoly> ctxt_tmp   = cryptoContext->EvalMult(ctxt_rotated_v, ptxt_current_diagonal);

        // t = add(t, tmp);
        if (i == 0) {
            ctxt_t = ctxt_tmp;
        }
        else {
            ctxt_t = cryptoContext->EvalAdd(ctxt_t, ctxt_tmp);
        }
    }

    // vec r = t;
    Ciphertext<DCRTPoly> ctxt_r = std::move(ctxt_t);

    for (int i = 0; i < log2_n_div_m; ++i) {
        // vec rotated_r = r;
        Ciphertext<DCRTPoly> ctxt_rotated_r = ctxt_r;

        // Calculate offset
        size_t offset = n / (2ULL << i);

        // rotated_r = rot(rotated_r, offset)
        ctxt_rotated_r = cryptoContext->EvalRotate(ctxt_rotated_r, offset);

        // r = add(r, rotated_r);
        ctxt_r = cryptoContext->EvalAdd(ctxt_r, ctxt_rotated_r);
    }
    //  r.resize(m); <- has to be done by the client
    // for efficiency we do not mask away the other entries
    enc_result = std::move(ctxt_r);
}

/// Create only the required power-of-two rotations
/// This can save quite a bit, for example for poly_modulus_degree = 16384
/// The default galois keys (with zlib compression) are 247 MB large
/// Whereas with dimension = 256, they are only 152 MB
/// For poly_modulus_degree = 32768, the default keys are 532 MB large
/// while with dimension = 256, they are only 304 MB
std::vector<int32_t> custom_steps(size_t dimension) {
    if (dimension == 256) {
        // Slight further optimization: No -128, no -256
        return {1, -1, 2, -2, 4, -4, 8, -8, 16, -16, 32, -32, 64, -64, 128, 256};
    }
    else {
        std::vector<int32_t> steps{};
        for (int i = 1; i <= dimension; i <<= 1) {
            steps.push_back(i);
            steps.push_back(-i);
        }
        return steps;
    }
}

/////
class DenseLayer {
private:
    std::vector<vec> diags;
    vec bias_vec;

public:
    /// Create random weights and biases for a dense or fully-connected layer
    /// \param units number of units, i.e. output size
    /// \param input_size dimension of input
    /// \throws std::invalid_argument if units != input_size because fast MVP is only defined over square matrices
    DenseLayer(size_t units, size_t input_size);

    /// Get Weights
    /// \return The weights matrix of size input_size x units, represented by its diagonals
    const std::vector<vec>& weights_as_diags();

    /// Get Weights
    /// \return A bias vector of length units
    const vec& bias();

    /// Get number of units
    size_t units();

    /// Get size of input
    size_t input_size();
};

DenseLayer::DenseLayer(size_t units, size_t input_size) {
    bias_vec = random_vector(units);
    diags    = std::vector<vec>();
    for (int i = 0; i < units; ++i) {
        diags.push_back(random_vector((input_size)));
    }
}

const std::vector<vec>& DenseLayer::weights_as_diags() {
    return diags;
}
const vec& DenseLayer::bias() {
    return bias_vec;
}

size_t DenseLayer::units() {
    return diags.size();
}
size_t DenseLayer::input_size() {
    return diags[0].size();
}

int main() {
    // Application setup
    /// Size of the input vector, i.e. flattened 32x32 image
    const size_t input_size = 1024;  // 32x32

    // We pad the MNIST images from 28x28 to 32x32
    // because of fast MVP we use requires that the input size divides # of units in the dense layers
    // and the result must be a power of two
    /// vectorized (padded) MNIST image
    std::vector<double> image = random_vector(input_size);

    // FHE Setup
    CCParams<CryptoContextCKKSRNS> parameters;
    parameters.SetSecurityLevel(SecurityLevel::HEStd_128_classic);
    parameters.SetMultiplicativeDepth(5);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    parameters.SetFirstModSize(60);
    parameters.SetScalingModSize(40);
    parameters.SetMaxRelinSkDeg(1);
    parameters.SetDigitSize(0);

    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);
    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    // Server.Keygen
    KeyPair<DCRTPoly> keyPair = cryptoContext->KeyGen();
    cryptoContext->EvalMultKeyGen(keyPair.secretKey);
    auto steps = custom_steps(1024);
    // TODO: we need to generate keys for rotations of {1, ..., d1.units()}
    for (int i = 1; i < 32; i++) {
        steps.push_back(i);
    }
    cryptoContext->EvalRotateKeyGen(keyPair.secretKey, steps);

    // Client.Encode, Client.Encrypt_pk
    auto image_ctxt = cryptoContext->Encrypt(keyPair.publicKey, cryptoContext->MakeCKKSPackedPlaintext(image));

    // Server.Encode, Server.Encrypt_sk
    DenseLayer d1(32, input_size);

    // First, compute the MVP between d1_weights and the input

    // PTXT check
    auto r = general_mvp_from_diagonals(d1.weights_as_diags(), image);
    // CTXT actual
    Ciphertext<DCRTPoly> result;
    ptxt_general_matrix_enc_vector_product(cryptoContext, d1.units(), d1.input_size(), d1.weights_as_diags(),
                                           image_ctxt, result);

    // Now add the bias
    Plaintext b1 = cryptoContext->MakeCKKSPackedPlaintext(d1.bias());
    cryptoContext->EvalAddInPlace(result, b1);

    // Rescale, since MVP does not rescale internally
    cryptoContext->RescaleInPlace(result);

    // Activation, x -> x^2
    cryptoContext->EvalSquareInPlace(result);
    cryptoContext->RelinearizeInPlace(result);
    cryptoContext->RescaleInPlace(result);

    // In order to fulfill the requirements for a "well rotatable" input vector, we must "duplicate" homomorphically
    Plaintext mask           = cryptoContext->MakeCKKSPackedPlaintext(vec(1, d1.units()));
    result                   = cryptoContext->EvalMult(result, mask);
    Ciphertext<DCRTPoly> tmp = cryptoContext->EvalRotate(result, d1.units());
    cryptoContext->EvalAddInPlace(tmp, result);
    cryptoContext->RescaleInPlace(tmp);

    // Create the Weights and Biases for the second  dense layer
    // We use 16, even though MNIST has only 10 classes, because of the power-of-two requirement
    // The model should have the weights for those 6 "dummy classes" forced to zero and the client can simply ignore them
    DenseLayer d2(16, d1.units());

    // Weights
    ptxt_general_matrix_enc_vector_product(cryptoContext, d2.units(), d2.input_size(), d2.weights_as_diags(), tmp,
                                           result);

    // Bias
    Plaintext b2 = cryptoContext->MakeCKKSPackedPlaintext(d2.bias());
    cryptoContext->EvalAddInPlace(result, b2);

    // Rescale, since MVP does not rescale internally
    cryptoContext->RescaleInPlace(result);

    // Activation, x -> x^2
    cryptoContext->EvalSquareInPlace(result);
    // No rescale or relinearize here, as we're done with the computation

    // Server.Decrypt
    Plaintext out;
    cryptoContext->Decrypt(keyPair.secretKey, result, &out);

    // Application checks
    cout << out << endl;

    return 0;
}