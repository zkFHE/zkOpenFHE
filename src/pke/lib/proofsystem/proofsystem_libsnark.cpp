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
    auto out = std::make_shared<LibsnarkProofMetadata>(ciphertext->GetElements().size());
    for (size_t i = 0; i < ciphertext->GetElements().size(); i++) {
        const auto c_i     = ciphertext->GetElements()[i];
        out->operator[](i) = vector<vector<pb_linear_combination<FieldT>>>(c_i.GetNumOfElements());
        for (size_t j = 0; j < c_i.GetNumOfElements(); j++) {
            const auto c_ij       = c_i.GetElementAtIndex(j);
            const auto& v_ij      = c_ij.GetValues();
            out->operator[](i)[j] = vector<pb_linear_combination<FieldT>>(v_ij.GetLength());

            for (size_t k = 0; k < v_ij.GetLength(); k++) {
                pb_variable<FieldT> tmp;
                tmp.allocate(pb);
                pb.val(tmp)              = v_ij[k].ConvertToInt<unsigned long>();
                out->operator[](i)[j][k] = pb_linear_combination<FieldT>(tmp);
            }
        }
    }
    SetProofMetadata(ciphertext, out);
    pb.set_input_sizes(pb.num_inputs() + (out->size() * out->operator[](0).size() * out->operator[](0)[0].size()));
}

void LibsnarkProofSystem::ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                            Ciphertext<DCRTPoly>& ctxt_out) {
    const auto in1 = *GetProofMetadata(ctxt1);
    const auto in2 = *GetProofMetadata(ctxt2);

    vector<unsigned long> moduli;
    for (const auto& e : ctxt_out->GetElements()[0].GetAllElements()) {
        moduli.push_back(e.GetModulus().ConvertToInt());
    }
    vector<BatchGadget<FieldT, AddModGadget<FieldT>>> add_mod_gadgets;
    LibsnarkProofMetadata out;
    assert(in1.size() == in2.size());
    for (size_t i = 0; i < in1.size(); i++) {
        add_mod_gadgets.emplace_back(pb, in1[i], in2[i], moduli);
        add_mod_gadgets[i].generate_r1cs_constraints();
        add_mod_gadgets[i].generate_r1cs_witness();
        out.push_back(add_mod_gadgets[i].get_output());
    }
    SetProofMetadata(ctxt_out, std::make_shared<LibsnarkProofMetadata>(out));
}

void LibsnarkProofSystem::ConstrainMultiplication(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                                  Ciphertext<DCRTPoly>& ctxt_out) {
    const auto in1 = *GetProofMetadata(ctxt1);
    const auto in2 = *GetProofMetadata(ctxt2);

    vector<unsigned long> moduli;
    for (const auto& e : ctxt_out->GetElements()[0].GetAllElements()) {
        moduli.push_back(e.GetModulus().ConvertToInt());
    }
    assert(in1.size() == ctxt1->GetElements().size() &&
           "mismatch between number of polynomial elements between ciphertext and metadata for input 1");
    assert(in2.size() == ctxt2->GetElements().size() &&
           "mismatch between number of polynomial elements between ciphertext and metadata for input 2");
    assert(in1.size() == in2.size() && "mismatch between number of polynomial elements between ciphertext inputs");
    assert(
        ctxt1->GetElements().size() == ctxt_out->GetElements().size() &&
        "mismatch between number of polynomial elements between ciphertext inputs and output. Are you using the FIXEDMANUAL scaling technique?");
    assert(in1.size() == 2);

    vector<BatchGadget<FieldT, MulModGadget<FieldT>>> mul_mod_gadgets;
    mul_mod_gadgets.reserve(2);
    vector<BatchGadget<FieldT, AddModGadget<FieldT>>> add_mod_gadgets;
    add_mod_gadgets.reserve(3);

    mul_mod_gadgets.emplace_back(pb, in1[0], in2[1], moduli);
    mul_mod_gadgets.emplace_back(pb, in1[1], in2[0], moduli);

    add_mod_gadgets.emplace_back(pb, in1[0], in2[0], moduli);
    add_mod_gadgets.emplace_back(pb, mul_mod_gadgets[0].get_output(), mul_mod_gadgets[1].get_output(), moduli);
    add_mod_gadgets.emplace_back(pb, in1[1], in2[1], moduli);

    for (auto& g : mul_mod_gadgets) {
        g.generate_r1cs_constraints();
        g.generate_r1cs_witness();
    }
    LibsnarkProofMetadata out;
    for (auto& g : add_mod_gadgets) {
        g.generate_r1cs_constraints();
        g.generate_r1cs_witness();
        out.push_back(g.get_output());
    }
    SetProofMetadata(ctxt_out, std::make_shared<LibsnarkProofMetadata>(out));
}

#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
