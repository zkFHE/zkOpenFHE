#ifndef OPENFHE_PROOFSYSTEM_H
#define OPENFHE_PROOFSYSTEM_H


#include "ciphertext.h"

using namespace lbcrypto;

 class ProofSystem {
public:
    virtual void ConstrainAddition(Ciphertext<DCRTPoly> ciphertext);
};

#endif  //OPENFHE_PROOFSYSTEM_H
