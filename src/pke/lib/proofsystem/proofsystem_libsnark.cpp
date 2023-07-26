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
    auto out           = std::make_shared<LibsnarkProofMetadata>(ciphertext->GetElements().size());
    out->modulus       = vector<size_t>(ciphertext->GetElements().size());
    out->curr_bit_size = vector<vector<size_t>>(ciphertext->GetElements().size());

    for (size_t j = 0; j < ciphertext->GetElements()[0].GetNumOfElements(); j++) {
        out->modulus[j] = ciphertext->GetElements()[0].GetElementAtIndex(j).GetModulus().ConvertToInt<unsigned long>();
    }

    for (size_t i = 0; i < ciphertext->GetElements().size(); i++) {
        const auto c_i        = ciphertext->GetElements()[i];
        out->operator[](i)    = vector<vector<pb_linear_combination<FieldT>>>(c_i.GetNumOfElements());
        out->curr_bit_size[i] = vector<size_t>(c_i.GetNumOfElements());
        for (size_t j = 0; j < c_i.GetNumOfElements(); j++) {
            const auto c_ij          = c_i.GetElementAtIndex(j);
            const auto& v_ij         = c_ij.GetValues();
            out->operator[](i)[j]    = vector<pb_linear_combination<FieldT>>(v_ij.GetLength());
            out->curr_bit_size[i][j] = c_ij.GetModulus().GetMSB();

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

    vector<size_t> out_bit_size(num_limbs);
    vector<bool> field_overflow(num_limbs);
    for (size_t j = 0; j < num_limbs; ++j) {
        out_bit_size[j]   = std::max(in1.curr_bit_size[index_1][j], in2.curr_bit_size[index_2][j]) + 1ul;
        field_overflow[j] = out_bit_size[j] >= FieldT::num_bits;
    }

    out.curr_bit_size[index_out] = vector<size_t>(out[index_out].size());
    for (size_t j = 0; j < num_limbs; ++j) {
        if (field_overflow[j]) {
            // Eager witness generation, add modulus constraints
            auto g =
                BatchGadget<FieldT, AddModGadget<FieldT>>(pb, in1[index_1][j], in1.curr_bit_size[index_1][j],
                                                          in2[index_2][j], in2.curr_bit_size[index_2][j], modulus[j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]               = g.get_output();
            out.curr_bit_size[index_out][j] = ceil(log2(out.modulus[j]));
        }
        else {
            // Lazy branch, do not add modulus constraints, but track size of values for later
            out[index_out][j] = vector<pb_linear_combination<FieldT>>(in1[index_1][j].size());
            for (size_t k = 0; k < out[index_out][j].size(); ++k) {
                out[index_out][j][k].assign(pb, in1[index_1][j][k] + in2[index_2][j][k]);
            }
            out.curr_bit_size[index_out][j] = out_bit_size[j];
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

    vector<size_t> out_bit_size(num_limbs);
    vector<bool> field_overflow(num_limbs);
    for (size_t j = 0; j < num_limbs; ++j) {
        out_bit_size[j]   = in1.curr_bit_size[index_1][j] + in2.curr_bit_size[index_2][j];
        field_overflow[j] = out_bit_size[j] >= FieldT::num_bits;
    }

    out.curr_bit_size[index_out] = vector<size_t>(num_limbs);
    for (size_t j = 0; j < num_limbs; ++j) {
        if (field_overflow[j]) {
            // Eager witness generation, add modulus constraints
            auto g =
                BatchGadget<FieldT, MulModGadget<FieldT>>(pb, in1[index_1][j], in1.curr_bit_size[index_1][j],
                                                          in2[index_2][j], in2.curr_bit_size[index_2][j], modulus[j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]               = g.get_output();
            out.curr_bit_size[index_out][j] = ceil(log2(out.modulus[j]));
        }
        else {
            // Lazy branch, only add quadratic constraint for multiplication without mod-reduction
            auto g = BatchGadget<FieldT, MulGadget<FieldT>>(pb, in1[index_1][j], in2[index_2][j]);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            out[index_out][j]               = g.get_output();
            out.curr_bit_size[index_out][j] = out_bit_size[j];
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
    out.curr_bit_size = vector<vector<size_t>>(in1.size());
    out.modulus       = in1.modulus;
    for (size_t i = 0; i < in1.size(); i++) {
        out[i] = vector<vector<pb_linear_combination<FieldT>>>(in1[i].size());
        constrain_addmod_lazy(in1, i, in2, i, out, i);
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
    auto out           = std::make_shared<LibsnarkProofMetadata>(ciphertext->GetElements().size());
    out->modulus       = vector<size_t>(ciphertext->GetElements().size());
    out->curr_bit_size = vector<vector<size_t>>(ciphertext->GetElements().size());

    for (size_t j = 0; j < ciphertext->GetElements()[0].GetNumOfElements(); j++) {
        out->modulus[j] = ciphertext->GetElements()[0].GetElementAtIndex(j).GetModulus().ConvertToInt<unsigned long>();
    }

    for (size_t i = 0; i < ciphertext->GetElements().size(); i++) {
        const auto c_i        = ciphertext->GetElements()[i];
        out->operator[](i)    = vector<vector<pb_linear_combination<FieldT>>>(c_i.GetNumOfElements());
        out->curr_bit_size[i] = vector<size_t>(c_i.GetNumOfElements());
        for (size_t j = 0; j < c_i.GetNumOfElements(); j++) {
            const auto c_ij          = c_i.GetElementAtIndex(j);
            const auto& v_ij         = c_ij.GetValues();
            out->operator[](i)[j]    = vector<pb_linear_combination<FieldT>>(v_ij.GetLength());
            out->curr_bit_size[i][j] = c_ij.GetModulus().GetMSB();

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
            bool needs_reduction = out.curr_bit_size[i][j] >= out.modulus[j];
            vector<pb_variable<FieldT>> vars(out[i][j].size());
            for (const auto& x : out_vars[i][j]) {
                assert(x.is_variable);
                vars.emplace_back(x.terms[0].index);
            }
            if (needs_reduction) {
                for (size_t k = 0; k < c_ij.GetLength(); ++k) {
                    auto g = BatchGadget<FieldT, ModAssignGadget<FieldT>>(pb, out[i][j], out.curr_bit_size[i][j],
                                                                          modulus[j], vars);
                    g.generate_r1cs_constraints();
                    g.generate_r1cs_witness();
                    out.curr_bit_size[i][j] = ceil(log2(out.modulus[j]));
                }
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

#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
