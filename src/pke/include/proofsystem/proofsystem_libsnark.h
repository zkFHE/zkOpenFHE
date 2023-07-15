#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_H
#define OPENFHE_PROOFSYSTEM_LIBSNARK_H

#include "proofsystem.h"
#include "libff/algebra/fields/field_utils.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/gadgetlib1/pb_variable.hpp"

typedef libff::Fr<libsnark::default_r1cs_ppzksnark_pp> FieldT;

class LibsnarkProofSystem : ProofSystem {

    libsnark::r1cs_constraint_system<FieldT> constraint_system;
    libsnark::protoboard<FieldT> protoboard;

    void ConstrainAddition(Ciphertext<DCRTPoly> ciphertext) override;


};
#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_H
