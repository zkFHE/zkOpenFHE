#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_H
#define OPENFHE_PROOFSYSTEM_LIBSNARK_H

#include "proofsystem.h"
#include "libff/algebra/fields/field_utils.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/gadgetlib1/pb_variable.hpp"
#include "key/evalkey.h"

#include <vector>
using std::vector;

using namespace libsnark;
typedef libff::Fr<default_r1cs_ppzksnark_pp> FieldT;

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
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::size;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::operator=;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::push_back;
    using vector<vector<vector<pb_linear_combination<FieldT>>>>::emplace_back;

    inline size_t get_bit_size(size_t i, size_t j) const {
        return max_value[i][j].as_bigint().num_bits();
    }
};

class LibsnarkProofSystem : ProofSystem {
protected:
    void constrain_addmod_lazy(const LibsnarkProofMetadata& in1, size_t index_1, const LibsnarkProofMetadata& in2,
                               size_t index_2, LibsnarkProofMetadata& out, size_t index_out);
    void constrain_submod_lazy(const LibsnarkProofMetadata& in1, size_t index_1, const LibsnarkProofMetadata& in2,
                               size_t index_2, LibsnarkProofMetadata& out, size_t index_out);
    void constrain_mulmod_lazy(const LibsnarkProofMetadata& in1, size_t index_1, const LibsnarkProofMetadata& in2,
                               size_t index_2, LibsnarkProofMetadata& out, size_t index_out);

public:
    protoboard<FieldT> pb;
    const CryptoContext<DCRTPoly> cryptoContext;

    explicit LibsnarkProofSystem(const CryptoContext<DCRTPoly>& cryptoContext) : cryptoContext(cryptoContext) {
        default_r1cs_ppzksnark_pp::init_public_params();
        pb = protoboard<FieldT>();
    }
    void ConstrainPublicInput(Ciphertext<DCRTPoly>& ciphertext) override;
    std::shared_ptr<LibsnarkProofMetadata> ConstrainPublicOutput(Ciphertext<DCRTPoly>& ciphertext);
    void ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                           Ciphertext<DCRTPoly>& ctxt_out) override;

    void ConstrainSubstraction(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                               Ciphertext<DCRTPoly>& ctxt_out) override;

    void ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                 Ciphertext<DCRTPoly>& ctxt_out) override;

    void ConstrainSquare(const Ciphertext<DCRTPoly>& ctxt, Ciphertext<DCRTPoly>& ctxt_out);

    template <typename VecType2>
    void ConstrainSetFormat(Format format, const VecType2& in, const VecType2& out,
                            const vector<pb_linear_combination<FieldT>>& in_lc, const FieldT& in_max_value,
                            vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value);

    void ConstrainSetFormat(Format format, const DCRTPoly& in, const DCRTPoly& out,
                            const vector<vector<pb_linear_combination<FieldT>>>& in_lc,
                            const vector<FieldT>& in_max_value, vector<vector<pb_linear_combination<FieldT>>>& out_lc,
                            vector<FieldT>& out_max_value);

    template <typename VecType, typename VecType2>
    void ConstrainNTT(const VecType& rootOfUnityTable, const VecType& preconRootOfUnityTable, const VecType2& element,
                      const VecType2& element_out, const vector<pb_linear_combination<FieldT>>& in_lc,
                      const FieldT& in_max_value, vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value);

    template <typename IntType, typename VecType, typename VecType2>
    void ConstrainINTT(const VecType& rootOfUnityInverseTable, const VecType& preconRootOfUnityInverseTable,
                       const IntType& cycloOrderInv, const IntType& preconCycloOrderInv, const VecType2& element,
                       const VecType2& element_out, const vector<pb_linear_combination<FieldT>>& in_lc,
                       const FieldT& in_max_value, vector<pb_linear_combination<FieldT>>& out_lc,
                       FieldT& out_max_value);

    template <typename VecType>
    void ConstrainSwitchModulus(const typename VecType::Integer& newModulus,
                                const typename VecType::Integer& rootOfUnity,
                                const typename VecType::Integer& modulusArb,
                                const typename VecType::Integer& rootOfUnityArb, const PolyImpl<VecType>& in,
                                const PolyImpl<VecType>& out, const vector<pb_linear_combination<FieldT>>& in_lc,
                                const FieldT& in_max_value, vector<pb_linear_combination<FieldT>>& out_lc,
                                FieldT& out_max_value);

    template <typename DCRTPoly>
    void ConstrainKeySwitchPrecomputeCore(const DCRTPoly& in,
                                          const std::shared_ptr<CryptoParametersBase<DCRTPoly>>& cryptoParamsBase,
                                          const std::shared_ptr<std::vector<DCRTPoly>>& out,
                                          const vector<vector<pb_linear_combination<FieldT>>>& in_lc,
                                          const vector<FieldT>& in_max_value,
                                          vector<vector<vector<pb_linear_combination<FieldT>>>>& out_lc,
                                          vector<vector<FieldT>>& out_max_value);

    template <typename DCRTPoly>
    void ConstrainFastKeySwitchCore(const EvalKey<DCRTPoly>& evalKey,
                                    const std::shared_ptr<typename DCRTPoly::Params>& paramsQl,
                                    const vector<vector<vector<pb_linear_combination<FieldT>>>>& in_lc,
                                    const vector<vector<FieldT>>& in_max_value,
                                    vector<vector<vector<pb_linear_combination<FieldT>>>>& out_lc,
                                    vector<vector<FieldT>>& out_max_value);

    template <typename DCRTPoly>
    void ConstrainFastKeySwitchCore(
        const std::shared_ptr<std::vector<DCRTPoly>>& digits, const EvalKey<DCRTPoly>& evalKey,
        const std::shared_ptr<typename DCRTPoly::Params>& paramsQl, std::shared_ptr<std::vector<DCRTPoly>>& out,
        const vector<vector<vector<pb_linear_combination<FieldT>>>>& in_lc, const vector<vector<FieldT>>& in_max_value,
        vector<vector<vector<pb_linear_combination<FieldT>>>>& out_lc, vector<vector<FieldT>>& out_max_value);

    template <typename DCRTPoly>
    void ConstrainRelin(const Ciphertext<DCRTPoly>& ciphertext, Ciphertext<DCRTPoly>& out);

    void FinalizeOutputConstraints(Ciphertext<DCRTPoly>& ctxt, const ProofMetadata& vars) override {
        FinalizeOutputConstraints(ctxt, dynamic_cast<const LibsnarkProofMetadata&>(vars));
    }

    void FinalizeOutputConstraints(Ciphertext<DCRTPoly>& ctxt, const LibsnarkProofMetadata& out_vars);

    static std::shared_ptr<LibsnarkProofMetadata> GetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext);

    static void SetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext,
                                 const std::shared_ptr<LibsnarkProofMetadata>& metadata);
};
#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_H
