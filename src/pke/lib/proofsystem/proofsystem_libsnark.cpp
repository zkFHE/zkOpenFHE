#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
#define OPENFHE_PROOFSYSTEM_LIBSNARK_CPP

#include "proofsystem/proofsystem_libsnark.h"
#include "proofsystem/gadgets_libsnark.h"

#include <vector>
#include <cassert>

#define LIBSNARK_PROOF_METADATA_KEY "libsnark_proof_metadata"

using namespace libsnark;
using std::cout, std::endl;
using std::vector;

std::shared_ptr<LibsnarkProofMetadata> LibsnarkProofSystem::GetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext) {
    auto it = ciphertext->FindMetadataByKey(LIBSNARK_PROOF_METADATA_KEY);
    if (ciphertext->MetadataFound(it)) {
        return std::dynamic_pointer_cast<LibsnarkProofMetadata>(ciphertext->GetMetadata(it));
    }
    else {
        OPENFHE_THROW(openfhe_error, "Attempt to access metadata (LibsnarkProofMetadata) that has not been set.");
    }
}

void LibsnarkProofSystem::SetProofMetadata(const Ciphertext<DCRTPoly>& ciphertext,
                                           const std::shared_ptr<LibsnarkProofMetadata>& metadata) {
    ciphertext->SetMetadataByKey(LIBSNARK_PROOF_METADATA_KEY, metadata);
}

void LibsnarkProofSystem::ConstrainPublicInput(Ciphertext<DCRTPoly>& ciphertext) {
    auto out       = std::make_shared<LibsnarkProofMetadata>(ciphertext->GetElements().size());
    out->modulus   = vector<size_t>(ciphertext->GetElements().size());
    out->max_value = vector<vector<FieldT>>(ciphertext->GetElements().size());

    for (size_t j = 0; j < ciphertext->GetElements()[0].GetNumOfElements(); j++) {
        out->modulus[j] = ciphertext->GetElements()[0].GetElementAtIndex(j).GetModulus().ConvertToInt<unsigned long>();
    }

    for (size_t i = 0; i < ciphertext->GetElements().size(); i++) {
        const auto c_i     = ciphertext->GetElements()[i];
        out->operator[](i) = vector<vector<pb_linear_combination<FieldT>>>(c_i.GetNumOfElements());
        out->max_value[i]  = vector<FieldT>(c_i.GetNumOfElements());
        for (size_t j = 0; j < c_i.GetNumOfElements(); j++) {
            const auto c_ij       = c_i.GetElementAtIndex(j);
            const auto& v_ij      = c_ij.GetValues();
            out->operator[](i)[j] = vector<pb_linear_combination<FieldT>>(v_ij.GetLength());
            out->max_value[i][j]  = FieldT(c_ij.GetModulus().ConvertToInt<unsigned long>()) - 1;

            for (size_t k = 0; k < v_ij.GetLength(); k++) {
                pb_variable<FieldT> tmp;
                tmp.allocate(pb, ciphertext->SerializedObjectName() + "[" + std::to_string(i) + "][" +
                                     std::to_string(j) + "][" + std::to_string(k) + "] (input)");
                pb.val(tmp)              = v_ij[k].ConvertToInt<unsigned long>();
                out->operator[](i)[j][k] = pb_linear_combination<FieldT>(tmp);
            }
        }
    }

    SetProofMetadata(ciphertext, out);
    pb.set_input_sizes(pb.num_inputs() + (out->size() * out->operator[](0).size() * out->operator[](0)[0].size()));
}

void LibsnarkProofSystem::constrain_addmod_lazy(const LibsnarkProofMetadata& in1, const size_t index_1,
                                                const LibsnarkProofMetadata& in2, const size_t index_2,
                                                LibsnarkProofMetadata& out, const size_t index_out) {
    assert(index_1 < in1.size());
    assert(index_2 < in2.size());
    assert(index_out < out.size());
    auto num_limbs = in1[index_1].size();
    assert(in2[index_2].size() == num_limbs);
    assert(out[index_out].size() == num_limbs);
    auto modulus = in1.modulus;
    assert(in2.modulus == modulus);
    assert(out.modulus == modulus && "modulus of `out' is not set");

    vector<FieldT> out_max_value(num_limbs);
    vector<bool> field_overflow(num_limbs);
    out.max_value[index_out] = vector<FieldT>(out[index_out].size());
    for (size_t j = 0; j < num_limbs; ++j) {
        size_t out_bit_size = std::max(in1.get_bit_size(index_1, j), in2.get_bit_size(index_2, j)) + 1ul;
        out_max_value[j]    = in1.max_value[index_1][j] + in2.max_value[index_2][j];
        field_overflow[j]   = out_bit_size >= FieldT::num_bits;

        if (field_overflow[j]) {
            // Eager witness generation, add modulus constraints
            auto g = BatchGadget<FieldT, AddModGadget<FieldT>>(pb, in1[index_1][j], in1.max_value[index_1][j],
                                                               in2[index_2][j], in2.max_value[index_2][j], modulus[j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]           = g.get_output();
            out.max_value[index_out][j] = FieldT(modulus[j]) - 1;
        }
        else {
            // Lazy branch, do not add modulus constraints, but track size of values for later
            out[index_out][j] = vector<pb_linear_combination<FieldT>>(in1[index_1][j].size());
            for (size_t k = 0; k < out[index_out][j].size(); ++k) {
                out[index_out][j][k].assign(pb, in1[index_1][j][k] + in2[index_2][j][k]);
            }
            out.max_value[index_out][j] = out_max_value[j];
        }
    }
}

void LibsnarkProofSystem::constrain_submod_lazy(const LibsnarkProofMetadata& in1, const size_t index_1,
                                                const LibsnarkProofMetadata& in2, const size_t index_2,
                                                LibsnarkProofMetadata& out, const size_t index_out) {
    assert(index_1 < in1.size());
    assert(index_2 < in2.size());
    assert(index_out < out.size());
    auto num_limbs = in1[index_1].size();
    assert(in2[index_2].size() == num_limbs);
    assert(out[index_out].size() == num_limbs);
    auto modulus = in1.modulus;
    assert(in2.modulus == modulus);
    assert(out.modulus == modulus && "modulus of `out' is not set");

    vector<FieldT> out_max_value(num_limbs);
    vector<bool> field_overflow(num_limbs);
    vector<bool> in2_lt_modulus(num_limbs);

    out.max_value[index_out] = vector<FieldT>(out[index_out].size());
    for (size_t j = 0; j < num_limbs; ++j) {
        out_max_value[j]    = in1.max_value[index_1][j] + FieldT(modulus[j]);
        size_t out_bit_size = std::max(in1.get_bit_size(index_1, j), (size_t)ceil(log2(modulus[j]))) + 1ul;
        field_overflow[j]   = out_bit_size >= FieldT::num_bits;
        in2_lt_modulus[j]   = lt(in2.max_value[index_2][j], FieldT(modulus[j]));

        auto in2_ij = in2[index_2][j];
        //        auto in2_ij_curr_bit_size = in2.get_bit_size(index_2, j);
        auto in2_ij_max_value = in2.max_value[index_2][j];
        if (!in2_lt_modulus[j]) {
            // We first need to mod-reduce in2[index_2][j][k] before we can compute its negative
            // TODO: is there a way to compute the negative from the lazy/non-reduced value directly?
            auto g_mod =
                BatchGadget<FieldT, ModGadget<FieldT>>(pb, in2[index_2][j], in2.max_value[index_2][j], modulus[j]);
            g_mod.generate_r1cs_constraints();
            g_mod.generate_r1cs_witness();

            in2_ij           = g_mod.get_output();
            in2_ij_max_value = FieldT(modulus[j]);
        }

        if (field_overflow[j]) {
            // Eager witness generation, add modulus constraints
            auto g = BatchGadget<FieldT, SubModGadget<FieldT>>(pb, in1[index_1][j], in1.max_value[index_1][j], in2_ij,
                                                               in2_ij_max_value, modulus[j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]           = g.get_output();
            out.max_value[index_out][j] = FieldT(modulus[j]) - 1;
        }
        else {
            // Lazy branch, do not add modulus constraints, but track size of values for later
            out[index_out][j] = vector<pb_linear_combination<FieldT>>(in1[index_1][j].size());
            for (size_t k = 0; k < out[index_out][j].size(); ++k) {
                out[index_out][j][k].assign(pb, in1[index_1][j][k] + FieldT(modulus[j]) - in2_ij[k]);
            }
            out.max_value[index_out][j] = out_max_value[j];
        }
    }
}

void LibsnarkProofSystem::constrain_mulmod_lazy(const LibsnarkProofMetadata& in1, const size_t index_1,
                                                const LibsnarkProofMetadata& in2, const size_t index_2,
                                                LibsnarkProofMetadata& out, const size_t index_out) {
    assert(index_1 < in1.size());
    assert(index_2 < in2.size());
    assert(index_out < out.size());
    auto num_limbs = in1[index_1].size();
    assert(in2[index_2].size() == num_limbs);
    assert(out[index_out].size() == num_limbs);
    auto modulus = in1.modulus;
    assert(in2.modulus == modulus);
    assert(out.modulus == modulus && "modulus of `out' is not set");

    vector<FieldT> out_max_value(num_limbs);
    vector<bool> field_overflow(num_limbs);
    out.max_value[index_out] = vector<FieldT>(num_limbs);
    for (size_t j = 0; j < num_limbs; ++j) {
        size_t out_bit_size = in1.get_bit_size(index_1, j) + in2.get_bit_size(index_2, j);
        out_max_value[j]    = in1.max_value[index_1][j] * in2.max_value[index_2][j];
        field_overflow[j]   = out_bit_size >= FieldT::num_bits;

        if (field_overflow[j]) {
            // Eager witness generation, add modulus constraints
            auto g = BatchGadget<FieldT, MulModGadget<FieldT>>(pb, in1[index_1][j], in1.max_value[index_1][j],
                                                               in2[index_2][j], in2.max_value[index_2][j], modulus[j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]           = g.get_output();
            out.max_value[index_out][j] = FieldT(modulus[j]) - 1;
        }
        else {
            // Lazy branch, only add quadratic constraint for multiplication without mod-reduction
            auto g = BatchGadget<FieldT, MulGadget<FieldT>>(pb, in1[index_1][j], in2[index_2][j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]           = g.get_output();
            out.max_value[index_out][j] = out_max_value[j];
        }
    }
}

void LibsnarkProofSystem::ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                            Ciphertext<DCRTPoly>& ctxt_out) {
    const auto in1 = *GetProofMetadata(ctxt1);
    const auto in2 = *GetProofMetadata(ctxt2);

    vector<unsigned long> moduli;
    for (const auto& e : ctxt_out->GetElements()[0].GetAllElements()) {
        moduli.push_back(e.GetModulus().ConvertToInt());
    }
    assert(in1.size() == in2.size());
    assert(in1.modulus == in2.modulus);
    assert(in1.modulus == moduli);

    LibsnarkProofMetadata out(in1.size());
    out.max_value = vector<vector<FieldT>>(in1.size());
    out.modulus   = in1.modulus;
    for (size_t i = 0; i < in1.size(); i++) {
        out[i] = vector<vector<pb_linear_combination<FieldT>>>(in1[i].size());
        constrain_addmod_lazy(in1, i, in2, i, out, i);
    }
    SetProofMetadata(ctxt_out, std::make_shared<LibsnarkProofMetadata>(out));
}

void LibsnarkProofSystem::ConstrainSubstraction(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                                Ciphertext<DCRTPoly>& ctxt_out) {
    const auto in1 = *GetProofMetadata(ctxt1);
    const auto in2 = *GetProofMetadata(ctxt2);

    vector<unsigned long> moduli;
    for (const auto& e : ctxt_out->GetElements()[0].GetAllElements()) {
        moduli.push_back(e.GetModulus().ConvertToInt());
    }
    assert(in1.size() == in2.size());
    assert(in1.modulus == in2.modulus);
    assert(in1.modulus == moduli);

    LibsnarkProofMetadata out(in1.size());
    out.max_value = vector<vector<FieldT>>(in1.size());
    out.modulus   = in1.modulus;
    for (size_t i = 0; i < in1.size(); i++) {
        out[i] = vector<vector<pb_linear_combination<FieldT>>>(in1[i].size());
        constrain_submod_lazy(in1, i, in2, i, out, i);
    }
    SetProofMetadata(ctxt_out, std::make_shared<LibsnarkProofMetadata>(out));
}

void LibsnarkProofSystem::ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                                  Ciphertext<DCRTPoly>& ctxt_out) {
    const auto in1 = *GetProofMetadata(ctxt1);
    const auto in2 = *GetProofMetadata(ctxt2);

    const auto num_limbs = in1.modulus.size();
    assert(in1.size() == ctxt1->GetElements().size() &&
           "mismatch between number of polynomial elements between ciphertext and metadata for input 1");
    assert(in2.size() == ctxt2->GetElements().size() &&
           "mismatch between number of polynomial elements between ciphertext and metadata for input 2");
    assert(in1.size() == in2.size() && "mismatch between number of polynomial elements between ciphertext inputs");
    assert(
        ctxt1->GetElements().size() == ctxt_out->GetElements().size() &&
        "mismatch between number of polynomial elements between ciphertext inputs and output. Are you using the FIXEDMANUAL scaling technique?");
    assert(in1.size() == 2);

    LibsnarkProofMetadata tmp(2);
    for (size_t i = 0; i < tmp.size(); i++) {
        tmp[i] = vector<vector<pb_linear_combination<FieldT>>>(num_limbs);
    }
    tmp.modulus = in1.modulus;
    constrain_mulmod_lazy(in1, 0, in2, 1, tmp, 0);
    constrain_mulmod_lazy(in1, 1, in2, 0, tmp, 1);

    LibsnarkProofMetadata out(3);
    for (size_t i = 0; i < out.size(); i++) {
        out[i] = vector<vector<pb_linear_combination<FieldT>>>(num_limbs);
    }
    out.modulus = in1.modulus;
    constrain_addmod_lazy(in1, 0, in2, 0, out, 0);
    constrain_addmod_lazy(tmp, 0, tmp, 1, out, 1);
    constrain_addmod_lazy(in1, 1, in2, 1, out, 2);
    SetProofMetadata(ctxt_out, std::make_shared<LibsnarkProofMetadata>(out));
}

std::shared_ptr<LibsnarkProofMetadata> LibsnarkProofSystem::ConstrainPublicOutput(Ciphertext<DCRTPoly>& ciphertext) {
    auto out       = std::make_shared<LibsnarkProofMetadata>(ciphertext->GetElements().size());
    out->modulus   = vector<size_t>(ciphertext->GetElements().size());
    out->max_value = vector<vector<FieldT>>(ciphertext->GetElements().size());

    for (size_t j = 0; j < ciphertext->GetElements()[0].GetNumOfElements(); j++) {
        out->modulus[j] = ciphertext->GetElements()[0].GetElementAtIndex(j).GetModulus().ConvertToInt<unsigned long>();
    }

    for (size_t i = 0; i < ciphertext->GetElements().size(); i++) {
        const auto c_i     = ciphertext->GetElements()[i];
        out->operator[](i) = vector<vector<pb_linear_combination<FieldT>>>(c_i.GetNumOfElements());
        out->max_value[i]  = vector<FieldT>(c_i.GetNumOfElements());
        for (size_t j = 0; j < c_i.GetNumOfElements(); j++) {
            const auto c_ij       = c_i.GetElementAtIndex(j);
            const auto& v_ij      = c_ij.GetValues();
            out->operator[](i)[j] = vector<pb_linear_combination<FieldT>>(v_ij.GetLength());
            out->max_value[i][j]  = FieldT(c_ij.GetModulus().ConvertToInt<size_t>()) - 1;

            for (size_t k = 0; k < v_ij.GetLength(); k++) {
                pb_variable<FieldT> tmp;
                tmp.allocate(pb, ciphertext->SerializedObjectName() + "[" + std::to_string(i) + "][" +
                                     std::to_string(j) + "][" + std::to_string(k) + "] (output)");
                out->operator[](i)[j][k] = pb_linear_combination<FieldT>(tmp);
            }
        }
    }

    pb.set_input_sizes(pb.num_inputs() + (out->size() * out->operator[](0).size() * out->operator[](0)[0].size()));
    return out;
}

void LibsnarkProofSystem::FinalizeOutputConstraints(Ciphertext<DCRTPoly>& ctxt, const LibsnarkProofMetadata& out_vars) {
    // ctxt holds metadata for the output of the computation, vars holds the (public input) variables allocated at the beginning of the computation
    // We resolve all pending lazy mod-reductions, and add constraints binding vars to the output of the computation
    auto out           = *GetProofMetadata(ctxt);
    const auto modulus = out.modulus;

    assert(ctxt->GetElements().size() == out_vars.size());
    for (size_t i = 0; i < ctxt->GetElements().size(); ++i) {
        auto c_i = ctxt->GetElements()[i];
        for (size_t j = 0; j < c_i.GetNumOfElements(); ++j) {
            auto c_ij            = c_i.GetElementAtIndex(j);
            bool needs_reduction = gt_eq(out.max_value[i][j], FieldT(out.modulus[j]));
            vector<pb_variable<FieldT>> vars;
            vars.reserve(out[i][j].size());
            for (const auto& x : out_vars[i][j]) {
                assert(x.is_variable);
                vars.emplace_back(x.terms[0].index);
            }
            if (needs_reduction) {
                auto g = BatchGadget<FieldT, ModAssignGadget<FieldT>>(
                    pb, out[i][j], out.max_value[i][j], modulus[j], vars,
                    "finalize_output_constraints[" + std::to_string(i) + "][" + std::to_string(j) + "]");
                g.generate_r1cs_constraints();
                g.generate_r1cs_witness();
                out.max_value[i][j] = FieldT(out.modulus[j]) - 1;
            }
            else {
                for (size_t k = 0; k < c_ij.GetLength(); ++k) {
                    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(out[i][j][k], 1, vars[k]),
                                           "finalize_output_constraints[" + std::to_string(i) + "][" +
                                               std::to_string(j) + "][" + std::to_string(k) + "]");
                }
            }
        }
    }
}

template <typename VecType>
void LibsnarkProofSystem::ConstrainSwitchModulus(
    const typename VecType::Integer& newModulus, const typename VecType::Integer& rootOfUnity,
    const typename VecType::Integer& modulusArb, const typename VecType::Integer& rootOfUnityArb,
    const PolyImpl<VecType>& in, const PolyImpl<VecType>& out, const vector<pb_linear_combination<FieldT>>& in_lc,
    const FieldT in_max_value, vector<pb_linear_combination<FieldT>>& out_lc, FieldT& out_max_value

) {
    /**Switches the integers in the vector to values corresponding to the new
 * modulus.
 * Algorithm: Integer i, Old Modulus om, New Modulus nm,
 * delta = abs(om-nm):
 *  Case 1: om < nm
 *    if i > om/2
 *      i' = i + delta
 *  Case 2: om > nm
 *    if i > om/2
 *      i' = i - delta
 */
    auto oldModulus(in.GetModulus());
    auto oldModulusByTwo(oldModulus >> 1);
    auto diff((oldModulus > newModulus) ? (oldModulus - newModulus) : (newModulus - oldModulus));

    assert(in_max_value.as_ulong() < oldModulus);  // Otherwise, we need to mod-reduce before
    if (newModulus > oldModulus) {
        for (usint i = 0; i < in.GetLength(); i++) {
            // b == [ in <= oldModulusByTwo ]
            // out == b * in + (1-b) * (in + diff), which we simplify to out == in + (1-b) * diff
            is_less_than_constant_gadget<FieldT> g(pb, in_lc[i], in_max_value.as_bigint().num_bits(),
                                                   FieldT(oldModulusByTwo.template ConvertToInt<unsigned long>()) + 1);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
                1, in_lc[i] + (1 - g.less_or_eq) * FieldT(diff.template ConvertToInt<unsigned long>()), out_lc[i]));
        }
    }
    else {
        assert(oldModulusByTwo > diff);  // If q/2 > q', then in-diff >= 0

        for (usint i = 0; i < in.GetLength(); i++) {
            // b == [ in <= oldModulusByTwo ]
            // tmp == b * in + (1-b) * (in - diff), which we simplify to tmp == in - (1-b) * diff
            // out == tmp (mod) newModulus
            is_less_than_constant_gadget<FieldT> g(pb, in_lc[i], in_max_value.as_bigint().num_bits(),
                                                   FieldT(oldModulusByTwo.template ConvertToInt<unsigned long>()) + 1);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            pb_variable<FieldT> tmp;
            tmp.allocate(pb, "tmp");
            pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
                1, in_lc[i] - (1 - g.less_or_eq) * FieldT(diff.template ConvertToInt<unsigned long>()), tmp));

            FieldT tmp_max_value =
                FieldT(std::max(oldModulusByTwo, oldModulus - 1 - diff).template ConvertToInt<unsigned long>());

            auto n        = in.GetValues()[i];
            auto sub_diff = (n > oldModulusByTwo) ? diff : 0;
            assert(n >= sub_diff);
            n           = n.Sub(sub_diff);
            pb.val(tmp) = FieldT(n.template ConvertToInt<unsigned long>());

            ModGadget<FieldT> g_mod(pb, tmp, tmp_max_value, newModulus.template ConvertToInt<unsigned long>(), "",
                                    false);
            out_lc[i] = g_mod.out;
            g_mod.generate_r1cs_constraints();

            g_mod.generate_r1cs_witness();
            assert(pb.lc_val(in_lc[i]) == FieldT(in.GetValues()[i].template ConvertToInt<unsigned long>()));
        }
    }
    out_max_value = newModulus.template ConvertToInt<unsigned long>() - 1;
}

template <typename IntType, typename VecType, typename VecType2>
vector<pb_linear_combination<FieldT>> LibsnarkProofSystem::ConstrainINTT(
    const VecType& rootOfUnityInverseTable, const VecType& preconRootOfUnityInverseTable, const IntType& cycloOrderInv,
    const IntType& preconCycloOrderInv, VecType2* element, VecType2* element_out, const LibsnarkProofMetadata in,
    size_t index_i, size_t index_j) {
    // Taken from ChineseRemainderTransformFTTNat<VecType>::InverseTransformFromBitReverseInPlace

    vector<pb_linear_combination<FieldT>> out_lc(in[index_i][index_j]);
    vector<FieldT> out_max_value(out_lc.size(), in.max_value[index_i][index_j]);

    usint n = element->GetLength();

    IntType modulus = element->GetModulus();

    IntType loVal, hiVal, omega, omegaFactor;
    NativeInteger preconOmega;
    usint i, m, j1, j2, indexOmega, indexLo, indexHi;

    usint t     = 1;
    usint logt1 = 1;
    for (m = (n >> 1); m >= 1; m >>= 1) {
        for (i = 0; i < m; ++i) {
            j1          = i << logt1;
            j2          = j1 + t;
            indexOmega  = m + i;
            omega       = rootOfUnityInverseTable[indexOmega];
            preconOmega = preconRootOfUnityInverseTable[indexOmega];

            for (indexLo = j1; indexLo < j2; ++indexLo) {
                // element_out[indexLo] = element[indexLo] + element[indexHi] (mod q)
                // element_out[indexHi] = (element[indexLo] - element[indexHi]) * omega (mod q)
                indexHi = indexLo + t;

                hiVal = (*element)[indexHi];
                loVal = (*element)[indexLo];

                omegaFactor = loVal;
                if (omegaFactor < hiVal) {
                    omegaFactor += modulus;
                }

                omegaFactor -= hiVal;

                loVal += hiVal;
                if (loVal >= modulus) {
                    loVal -= modulus;
                }

                omegaFactor.ModMulFastConstEq(omega, modulus, preconOmega);

                LazyAddModGadget<FieldT> g1(this->pb, out_lc[indexLo], out_max_value[indexLo], out_lc[indexHi],
                                            out_max_value[indexHi], modulus.ConvertToInt());
                LazySubModGadget<FieldT> g2(this->pb, out_lc[indexLo], out_max_value[indexLo], out_lc[indexHi],
                                            out_max_value[indexHi], modulus.ConvertToInt());
                LazyMulModGadget<FieldT> g3(this->pb, out_lc[indexLo], out_max_value[indexLo],
                                            FieldT(omegaFactor.ConvertToInt()), modulus.ConvertToInt());
                g1.generate_r1cs_constraints();
                g1.generate_r1cs_witness();

                g2.generate_r1cs_constraints();
                g2.generate_r1cs_witness();
                g3.generate_r1cs_constraints();
                g3.generate_r1cs_witness();

                out_lc[indexLo]        = g1.out;
                out_max_value[indexLo] = g1.out_max_value;

                out_lc[indexHi]        = g3.out;
                out_max_value[indexHi] = g3.out_max_value;

                (*element)[indexLo] = loVal;
                (*element)[indexHi] = omegaFactor;
            }
        }
        t <<= 1;
        logt1++;
    }

    for (i = 0; i < n; i++) {
        (*element)[i].ModMulFastConstEq(cycloOrderInv, modulus, preconCycloOrderInv);
        LazyMulModGadget<FieldT> g(this->pb, out_lc[i], out_max_value[i], FieldT(cycloOrderInv.ConvertToInt()),
                                   modulus.ConvertToInt());
        g.generate_r1cs_constraints();
        g.generate_r1cs_witness();
        out_lc[i]        = g.out;
        out_max_value[i] = g.out_max_value;
    }
    return out_lc;
}
#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
