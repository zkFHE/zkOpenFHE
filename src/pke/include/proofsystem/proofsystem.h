#ifndef OPENFHE_PROOFSYSTEM_H
#define OPENFHE_PROOFSYSTEM_H

#include "ciphertext.h"

using namespace lbcrypto;

class ProofMetadata : public Metadata {};
class ProofSystem {
public:
    virtual void ConstrainPublicInput(Ciphertext<DCRTPoly>& ciphertext) {}
    virtual void ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                   Ciphertext<DCRTPoly>& ctxt_out) {}
    virtual void ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                         Ciphertext<DCRTPoly>& ctxt_out) {}
};

#endif  //OPENFHE_PROOFSYSTEM_H
