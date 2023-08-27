#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_H
#define OPENFHE_PROOFSYSTEM_LIBSNARK_H

#include "proofsystem.h"
#include "libff/algebra/fields/field_utils.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/gadgetlib1/pb_variable.hpp"
#include "gadgets_libsnark.h"
#include "key/evalkey.h"

#include <vector>
using std::vector;

using namespace libsnark;
typedef libff::Fr<default_r1cs_ppzksnark_pp> FieldT;

enum PROOFSYSTEM_MODE {
    PROOFSYSTEM_MODE_CONSTRAINT_GENERATION,
    PROOFSYSTEM_MODE_WITNESS_GENERATION,
};

class LibsnarkProofMetadata : public ProofMetadata, private vector<vector<vector<pb_linear_combination<FieldT>>>> {
public:
    vector<size_t> modulus;
    vector<vector<FieldT>> max_value;

    explicit LibsnarkProofMetadata(size_t n = 0)
        : ProofMetadata(), vector<vector<vector<pb_linear_combination<FieldT>>>>(n), modulus(0), max_value(n) {}

    explicit LibsnarkProofMetadata(const vector<vector<vector<pb_linear_combination<FieldT>>>>& pb_linear_combinations)
        : ProofMetadata(),
          vector<vector<vector<pb_linear_combination<FieldT>>>>(pb_linear_combinations),
          modulus(pb_linear_combinations.size()),
          max_value(pb_linear_combinations.size()) {}

    using vector<vector<vector<pb_linear_combination<FieldT>>>>::vector;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::operator[];
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::at;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::size;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::operator=;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::push_back;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::emplace_back;

    inline size_t get_bit_size(size_t i, size_t j) const {
        return max_value[i][j].as_bigint().num_bits();
    }
};

using LibsnarkConstraintMetadata = LibsnarkProofMetadata;

class LibsnarkWitnessMetadata : public Metadata {
    //    vector<vector<vector<size_t>>> variable_indices;
public:
    size_t index_start;
    std::shared_ptr<protoboard<FieldT>> pb;
    vector<std::shared_ptr<gadget_gen<FieldT>>> gadgets;
};

using WireID = std::string;

class WireIdMetadata : public Metadata {
public:
    const WireID wire_id;

    WireIdMetadata(const WireID& wireId) : wire_id(wireId) {}
};

class LibsnarkProofSystem : ProofSystem {
protected:
    void constrain_addmod_lazy(const LibsnarkProofMetadata& in1, size_t index_1, const LibsnarkProofMetadata& in2,
                               size_t index_2, LibsnarkProofMetadata& out, size_t index_out);
    void constrain_submod_lazy(const LibsnarkProofMetadata& in1, size_t index_1, const LibsnarkProofMetadata& in2,
                               size_t index_2, LibsnarkProofMetadata& out, size_t index_out);
    void constrain_mulmod_lazy(const LibsnarkProofMetadata& in1, size_t index_1, const LibsnarkProofMetadata& in2,
                               size_t index_2, LibsnarkProofMetadata& out, size_t index_out);
    std::unordered_map<WireID, LibsnarkWitnessMetadata> wire_metadata;
    static size_t global_wire_id;

public:
    protoboard<FieldT> pb;
    const CryptoContext<DCRTPoly> cryptoContext;
    PROOFSYSTEM_MODE mode;

    explicit LibsnarkProofSystem(const CryptoContext<DCRTPoly>& cryptoContext) : cryptoContext(cryptoContext) {
        default_r1cs_ppzksnark_pp::init_public_params();
    }

    void SetMode(PROOFSYSTEM_MODE mode) {
        this->mode           = mode;
        this->global_wire_id = 0;
        if (mode == PROOFSYSTEM_MODE_CONSTRAINT_GENERATION) {
            pb = protoboard<FieldT>();
        }
    }

    static size_t get_next_wire_id() {
        return global_wire_id++;
    }

    void ConstrainPublicInput(Ciphertext<DCRTPoly>& ciphertext) override;
    void GenConstraintPublicInput(const Ciphertext<DCRTPoly>& ciphertext);
    void GenWitnessPublicInput(Ciphertext<DCRTPoly>& ciphertext);

    std::shared_ptr<LibsnarkProofMetadata> ConstrainPublicOutput(Ciphertext<DCRTPoly>& ciphertext);
    void ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                           Ciphertext<DCRTPoly>& ctxt_out) override;
    void GenConstraintAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                               Ciphertext<DCRTPoly>& ctxt_out);
    void GenWitnessAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                            Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt, const Plaintext& ptxt, Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainSubstraction(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                               Ciphertext<DCRTPoly>& ctxt_out) override;
    void GenConstraintSubstraction(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                   Ciphertext<DCRTPoly>& ctxt_out);
    void GenWitnessSubstraction(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                 Ciphertext<DCRTPoly>& ctxt_out) override;
    void GenConstraintMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                     Ciphertext<DCRTPoly>& ctxt_out);
    void GenWitnessMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                  Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainSquare(const Ciphertext<DCRTPoly>& ctxt, Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainSquare2(const Ciphertext<DCRTPoly>& ctxt, Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainRescale(const Ciphertext<DCRTPoly>& ctxt, Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainSetFormat(Format format, const DCRTPoly::PolyType& in, const DCRTPoly::PolyType& out,
                            const vector<pb_linear_combination<FieldT>>& in_lc, const FieldT& in_max_value,
                            vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value);

    void ConstrainSetFormat(Format format, const DCRTPoly& in, const DCRTPoly& out,
                            const vector<vector<pb_linear_combination<FieldT>>>& in_lc,
                            const vector<FieldT>& in_max_value, vector<vector<pb_linear_combination<FieldT>>>& out_lc,
                            vector<FieldT>& out_max_value);

    void ConstrainNTTClassic(const DCRTPoly::PolyType::Vector& rootOfUnityTable,
                             const DCRTPoly::PolyType::Vector& preconRootOfUnityTable,
                             const DCRTPoly::PolyType& element_in, const DCRTPoly::PolyType& element_out,
                             const vector<pb_linear_combination<FieldT>>& in_lc, const FieldT& in_max_value,
                             vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value);

    void ConstrainNTT(const DCRTPoly::PolyType::Vector& rootOfUnityTable,
                      const DCRTPoly::PolyType::Vector& preconRootOfUnityTable, const DCRTPoly::PolyType& element_in,
                      const DCRTPoly::PolyType& element_out

                      ,
                      const vector<pb_linear_combination<FieldT>>& in_lc, const FieldT& in_max_value,
                      vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value);

    void ConstrainINTT(const DCRTPoly::PolyType::Vector& rootOfUnityInverseTable,
                       const DCRTPoly::PolyType::Vector& preconRootOfUnityInverseTable,
                       const DCRTPoly::PolyType::Vector::Integer& cycloOrderInv,
                       const DCRTPoly::PolyType::Vector::Integer& preconCycloOrderInv,
                       const DCRTPoly::PolyType& element, const DCRTPoly::PolyType& element_out,
                       const vector<pb_linear_combination<FieldT>>& in_lc, const FieldT& in_max_value,
                       vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value);

    void ConstrainSwitchModulus(const DCRTPoly::PolyType::Vector::Integer& newModulus,
                                const DCRTPoly::PolyType::Vector::Integer& rootOfUnity,
                                const DCRTPoly::PolyType::Vector::Integer& modulusArb,
                                const DCRTPoly::PolyType::Vector::Integer& rootOfUnityArb, const DCRTPoly::PolyType& in,
                                const DCRTPoly::PolyType& out, const vector<pb_linear_combination<FieldT>>& in_lc,
                                const FieldT& in_max_value, vector<pb_linear_combination<FieldT>>& out_lc,
                                FieldT& out_max_value);

    void ConstrainKeySwitchPrecomputeCore(const DCRTPoly& in,
                                          const std::shared_ptr<CryptoParametersBase<DCRTPoly>>& cryptoParamsBase,
                                          const std::shared_ptr<std::vector<DCRTPoly>>& out,
                                          const vector<vector<pb_linear_combination<FieldT>>>& in_lc,
                                          const vector<FieldT>& in_max_value,
                                          vector<vector<vector<pb_linear_combination<FieldT>>>>& out_lc,
                                          vector<vector<FieldT>>& out_max_value);

    void ConstrainFastKeySwitchCore(const EvalKey<DCRTPoly>& evalKey, const std::shared_ptr<DCRTPoly::Params>& paramsQl,
                                    const vector<vector<vector<pb_linear_combination<FieldT>>>>& in_lc,
                                    const vector<vector<FieldT>>& in_max_value,
                                    vector<vector<vector<pb_linear_combination<FieldT>>>>& out_lc,
                                    vector<vector<FieldT>>& out_max_value);

    void ConstrainFastKeySwitchCore(const std::shared_ptr<std::vector<DCRTPoly>>& digits,
                                    const EvalKey<DCRTPoly>& evalKey, const std::shared_ptr<DCRTPoly::Params>& paramsQl,
                                    std::shared_ptr<std::vector<DCRTPoly>>& out,
                                    const vector<vector<vector<pb_linear_combination<FieldT>>>>& in_lc,
                                    const vector<vector<FieldT>>& in_max_value,
                                    vector<vector<vector<pb_linear_combination<FieldT>>>>& out_lc,
                                    vector<vector<FieldT>>& out_max_value);

    void ConstrainRelin(const Ciphertext<DCRTPoly>& ciphertext, Ciphertext<DCRTPoly>& out);

    void FinalizeOutputConstraints(Ciphertext<DCRTPoly>& ctxt, const ProofMetadata& vars) override {
        FinalizeOutputConstraints(ctxt, dynamic_cast<const LibsnarkProofMetadata&>(vars));
    }

    void FinalizeOutputConstraints(Ciphertext<DCRTPoly>& ctxt, const LibsnarkProofMetadata& out_vars);

    static std::shared_ptr<LibsnarkProofMetadata> GetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext);

    static void SetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext,
                                 const std::shared_ptr<LibsnarkProofMetadata>& metadata);

    void ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Plaintext& ptxt2,
                                 Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainRotate(const Ciphertext<DCRTPoly>& ciphertext, int rot_idx, Ciphertext<DCRTPoly>& ctxt_out);
    void ConstrainSubstraction(const Ciphertext<DCRTPoly>& ctxt1, const Plaintext& ptxt,
                               Ciphertext<DCRTPoly>& ctxt_out);

    void ConstrainKeySwitch(const Ciphertext<DCRTPoly>& ctxt_i, const EvalKey<DCRTPoly>& evalKey,
                            Ciphertext<DCRTPoly>& ctxt_out);
    void ConstrainNTTOpt(const intnat::NativeVectorT<NativeInteger>& rootOfUnityTable,
                         const intnat::NativeVectorT<NativeInteger>& preconRootOfUnityTable,
                         const DCRTPoly::PolyType& element_in, const DCRTPoly::PolyType& element_out,
                         const vector<FieldT>& in_lc, const FieldT& in_max_value, vector<FieldT>& out_lc,
                         FieldT& out_max_value);
    WireID GetWireID(const Ciphertext<DCRTPoly>& ciphertext);
    void SetWireId(const Ciphertext<DCRTPoly>& ciphertext, const WireID& wire_id);
};

size_t LibsnarkProofSystem::global_wire_id = 0;

#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_H
