#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_H
#define OPENFHE_PROOFSYSTEM_LIBSNARK_H

#include "proofsystem.h"
#include "libff/algebra/fields/field_utils.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/gadgetlib1/pb_variable.hpp"
#include <vector>
using std::vector;

using namespace libsnark;
typedef libff::Fr<default_r1cs_ppzksnark_pp> FieldT;

class LibsnarkProofMetadata : public ProofMetadata, private vector<vector<vector<pb_linear_combination<FieldT>>>> {
public:
    vector<size_t> modulus;
    vector<size_t> curr_bit_size;

    explicit LibsnarkProofMetadata()
        : ProofMetadata(), vector<vector<vector<pb_linear_combination<FieldT>>>>(), modulus(0), curr_bit_size(0) {}

    explicit LibsnarkProofMetadata(const vector<vector<vector<pb_linear_combination<FieldT>>>>& pb_linear_combinations)
        : ProofMetadata(),
          vector<vector<vector<pb_linear_combination<FieldT>>>>(pb_linear_combinations),
          modulus(pb_linear_combinations.size()),
          curr_bit_size(pb_linear_combinations.size()) {}

    using vector<vector<vector<pb_linear_combination<FieldT>>>>::vector;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::operator[];
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::size;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::operator=;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::push_back;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::emplace_back;
};

class LibsnarkProofSystem : ProofSystem {
public:
    protoboard<FieldT> pb;

    LibsnarkProofSystem() {
        default_r1cs_ppzksnark_pp::init_public_params();
        pb = protoboard<FieldT>();
    }
    void ConstrainPublicInput(Ciphertext<DCRTPoly>& ciphertext) override;
    void ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                           Ciphertext<DCRTPoly>& ctxt_out) override;
    void ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                 Ciphertext<DCRTPoly>& ctxt_out) override;
    static std::shared_ptr<LibsnarkProofMetadata> GetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext);
    static void SetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext,
                                 const std::shared_ptr<LibsnarkProofMetadata>& metadata);
};
#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_H
