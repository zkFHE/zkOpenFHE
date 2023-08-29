//==================================================================================
// BSD 2-Clause License
//
// Copyright (c) 2014-2022, NJIT, Duality Technologies Inc. and other contributors
//
// All rights reserved.
//
// Author TPOC: contact@openfhe.org
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this
//    list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright notice,
//    this list of conditions and the following disclaimer in the documentation
//    and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//==================================================================================

/*
  Simple example for BGVrns (integer arithmetic)
 */

#include "openfhe.h"
#include "proofsystem/proofsystem_libsnark.h"
#include <iostream>
#include "proofsystem/gadgets_libsnark.h"

using std::cout, std::endl;
using namespace lbcrypto;

int main() {
    libff::default_ec_pp::init_public_params();

    // Sample Program: Step 1 - Set CryptoContext
    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(1);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    parameters.SetKeySwitchTechnique(
        KeySwitchTechnique::
            BV);  // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs

    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);
    // Enable features that you wish to use
    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);
    EvalKey<DCRTPoly> x;

    // Sample Program: Step 2 - Key Generation

    // Initialize Public Key Containers
    KeyPair<DCRTPoly> keyPair;

    // Generate a public/private key pair
    keyPair = cryptoContext->KeyGen();

    // Generate the relinearization key
    cryptoContext->EvalMultKeyGen(keyPair.secretKey);

    // Generate the rotation evaluation keys
    cryptoContext->EvalRotateKeyGen(keyPair.secretKey, {1, 2, -1, -2});

    // Print parameters
    cout << "N: " << cryptoContext->GetRingDimension() << endl;
    cout << "t: " << cryptoContext->GetCryptoParameters()->GetPlaintextModulus() << endl;
    cout << "Q: " << cryptoContext->GetCryptoParameters()->GetElementParams()->GetModulus() << endl;
    cout << "KeySwitchTechnique: " << parameters.GetKeySwitchTechnique() << endl;
    cout << "DigitSize: " << parameters.GetDigitSize() << endl;

    // Sample Program: Step 3 - Encryption

    // First plaintext vector is encoded
    std::vector<int64_t> vectorOfInts1 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
    Plaintext plaintext1               = cryptoContext->MakePackedPlaintext(vectorOfInts1);
    // Second plaintext vector is encoded
    std::vector<int64_t> vectorOfInts2 = {3, 2, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12};
    Plaintext plaintext2               = cryptoContext->MakePackedPlaintext(vectorOfInts2);
    // Third plaintext vector is encoded
    std::vector<int64_t> vectorOfInts3 = {1, 2, 5, 2, 5, 6, 7, 8, 9, 10, 11, 12};
    Plaintext plaintext3               = cryptoContext->MakePackedPlaintext(vectorOfInts3);

    // The encoded vectors are encrypted
    auto ciphertext1 = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);
    auto ciphertext2 = cryptoContext->Encrypt(keyPair.publicKey, plaintext2);
    auto ciphertext3 = cryptoContext->Encrypt(keyPair.publicKey, plaintext3);

    cout << "Encryption: done" << endl;
    // Sample Program: Step 4 - Evaluation

    Ciphertext<DCRTPoly> ctxt_out;

    // Homomorphic additions
    auto ciphertextAdd12 = cryptoContext->EvalAdd(ciphertext1, ciphertext2);
    auto ciphertextSub12 = cryptoContext->EvalSub(ciphertext1, ciphertext2);

    auto ciphertextRot = cryptoContext->EvalRotate(ciphertext1, 1);

    auto ciphertextMul = cryptoContext->EvalMultNoRelin(ciphertextAdd12, ciphertextSub12);

    auto ciphertextRelin = cryptoContext->Relinearize(ciphertextMul);

    //////

    LibsnarkProofSystem ps(nullptr, cryptoContext);

    ps.ConstrainPublicInput(ciphertext1);
    ps.ConstrainPublicInput(ciphertext2);
    // TODO important: only add public input before adding any other constraints!
    auto vars_out = *ps.ConstrainPublicOutput(ciphertextMul);

    ps.EvalAdd(ciphertext1, ciphertext2, ciphertextAdd12);
    ps.ConstrainSubstraction(ciphertext1, ciphertext2, ciphertextSub12);
    ps.EvalMultNoRelin(ciphertextAdd12, ciphertextSub12, ciphertextMul);
    ps.ConstrainRelin(ciphertextMul, ciphertextRelin);
    ps.FinalizeOutputConstraints(ciphertextMul, vars_out);

    ////////////////////////

    const auto pb                                          = ps.pb;
    const r1cs_constraint_system<FieldT> constraint_system = ps.pb.get_constraint_system();

    cout << "#inputs:      " << constraint_system.num_inputs() << endl;
    cout << "#variables:   " << constraint_system.num_variables() << endl;
    cout << "#constraints: " << constraint_system.num_constraints() << endl;

    bool satisfied = constraint_system.is_satisfied(pb.primary_input(), pb.auxiliary_input());
    cout << "satisfied:    " << std::boolalpha << satisfied << endl;
    return !satisfied;

    //    r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp> keypair = r1cs_ppzksnark_generator<default_r1cs_ppzksnark_pp>(constraint_system);
    //
    //    r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp> proof = r1cs_ppzksnark_prover<default_r1cs_ppzksnark_pp>(keypair.pk, pb.primary_input(), pb.auxiliary_input());
    //    bool verified = r1cs_ppzksnark_verifier_strong_IC<default_r1cs_ppzksnark_pp>(keypair.vk, pb.primary_input(), proof);
    //    cout << "VERIFICATION: " << verified << endl;
    ////////////////////

    auto ciphertextAddResult = cryptoContext->EvalAdd(ciphertextAdd12, ciphertext3);

    // Homomorphic multiplications
    // modulus switching is done automatically because by default the modulus
    // switching method is set to AUTO (rather than MANUAL)
    auto ciphertextMul12      = cryptoContext->EvalMult(ciphertext1, ciphertext2);
    auto ciphertextMultResult = cryptoContext->EvalMult(ciphertextMul12, ciphertext3);
    // Homomorphic rotations
    auto ciphertextRot1 = cryptoContext->EvalRotate(ciphertext1, 1);
    auto ciphertextRot2 = cryptoContext->EvalRotate(ciphertext1, 2);
    auto ciphertextRot3 = cryptoContext->EvalRotate(ciphertext1, -1);
    auto ciphertextRot4 = cryptoContext->EvalRotate(ciphertext1, -2);

    // Sample Program: Step 5 - Decryption

    // Decrypt the result of additions
    Plaintext plaintextAddResult;
    cryptoContext->Decrypt(keyPair.secretKey, ciphertextAddResult, &plaintextAddResult);

    // Decrypt the result of multiplications
    Plaintext plaintextMultResult;
    cryptoContext->Decrypt(keyPair.secretKey, ciphertextMultResult, &plaintextMultResult);

    // Decrypt the result of rotations
    Plaintext plaintextRot1;
    cryptoContext->Decrypt(keyPair.secretKey, ciphertextRot1, &plaintextRot1);
    Plaintext plaintextRot2;
    cryptoContext->Decrypt(keyPair.secretKey, ciphertextRot2, &plaintextRot2);
    Plaintext plaintextRot3;
    cryptoContext->Decrypt(keyPair.secretKey, ciphertextRot3, &plaintextRot3);
    Plaintext plaintextRot4;
    cryptoContext->Decrypt(keyPair.secretKey, ciphertextRot4, &plaintextRot4);

    plaintextRot1->SetLength(vectorOfInts1.size());
    plaintextRot2->SetLength(vectorOfInts1.size());
    plaintextRot3->SetLength(vectorOfInts1.size());
    plaintextRot4->SetLength(vectorOfInts1.size());

    std::cout << "Plaintext #1: " << plaintext1 << std::endl;
    std::cout << "Plaintext #2: " << plaintext2 << std::endl;
    std::cout << "Plaintext #3: " << plaintext3 << std::endl;

    // Output results
    std::cout << "\nResults of homomorphic computations" << std::endl;
    std::cout << "#1 + #2 + #3: " << plaintextAddResult << std::endl;
    std::cout << "#1 * #2 * #3: " << plaintextMultResult << std::endl;
    std::cout << "Left rotation of #1 by 1: " << plaintextRot1 << std::endl;
    std::cout << "Left rotation of #1 by 2: " << plaintextRot2 << std::endl;
    std::cout << "Right rotation of #1 by 1: " << plaintextRot3 << std::endl;
    std::cout << "Right rotation of #1 by 2: " << plaintextRot4 << std::endl;

    return 0;
}
