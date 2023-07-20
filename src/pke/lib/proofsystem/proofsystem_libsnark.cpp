#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
#define OPENFHE_PROOFSYSTEM_LIBSNARK_CPP

#include "proofsystem/proofsystem_libsnark.h"
#include "libsnark/gadgetlib1/gadget.hpp"
#include "libsnark/gadgetlib2/gadget.hpp"
#include "libsnark/gadgetlib1/gadgets/basic_gadgets.hpp"
#include <vector>
#include <cassert>

#define LIBSNARK_PROOF_METADATA_KEY "libsnark_proof_metadata"

using namespace libsnark;
using std::vector;

template <typename FieldT>
class less_than_constant_gadget : public gadget<FieldT> {
private:
    pb_variable_array<FieldT> alpha;
    pb_variable<FieldT> alpha_packed;
    std::shared_ptr<packing_gadget<FieldT>> pack_alpha;

    pb_variable<FieldT> not_all_zeros;

public:
    const size_t n;
    const pb_linear_combination<FieldT> A;
    const FieldT B;
    pb_variable<FieldT> less_or_eq;

    less_than_constant_gadget(protoboard<FieldT>& pb, const size_t n, const pb_linear_combination<FieldT>& A,
                              const FieldT& B, const std::string& annotation_prefix = "")
        : gadget<FieldT>(pb, annotation_prefix), n(n), A(A), B(B) {
        less_or_eq.allocate(pb);
        alpha.allocate(pb, n);
        alpha.emplace_back(less_or_eq);  // alpha[n] is less_or_eq

        alpha_packed.allocate(pb);

        pack_alpha.reset(new packing_gadget<FieldT>(pb, alpha, alpha_packed));
    };

    void generate_r1cs_constraints();
    void generate_r1cs_witness();
};

template <typename FieldT>
void less_than_constant_gadget<FieldT>::generate_r1cs_constraints() {
    /* constraints for packed(alpha) = 2^n + B - A */
    pack_alpha->generate_r1cs_constraints(true);
    this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, (FieldT(2) ^ n) + (B - 1) - A, alpha_packed));
}

template <typename FieldT>
void less_than_constant_gadget<FieldT>::generate_r1cs_witness() {
    A.evaluate(this->pb);
    assert(B.as_bigint().num_bits() < n && "assumption that B has n bits violated in less_than_constant_gadget");
    // TODO: add assert for exact comparison A < B, not only by comparing bit-sizes
    assert(this->pb.lc_val(A).as_bigint().num_bits() <= B.as_bigint().num_bits() &&
           "less_than_constant constraint does not hold");

    /* unpack 2^n + B - A into alpha_packed */
    this->pb.val(alpha_packed) = (FieldT(2) ^ n) + (B - 1) - this->pb.lc_val(A);
    pack_alpha->generate_r1cs_witness_from_packed();

    // We fix less_or_eq == alpha[n] to be 1
    assert(this->pb.val(less_or_eq) == 1 &&
           "less_or_eq bit is not set to 1 with current assignment, constraints will not be satisfied");
    this->pb.val(less_or_eq) = 1;
}

template <typename FieldT>
class AddModGadget : public gadget<FieldT> {
public:
    std::shared_ptr<less_than_constant_gadget<FieldT>> lt_constant;
    size_t modulus;
    pb_linear_combination<FieldT> in1, in2;
    pb_variable<FieldT> out, quotient;

    AddModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1,
                 const pb_linear_combination<FieldT> in2, size_t modulus, const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, annotationPrefix), modulus(modulus), in1(in1), in2(in2) {
        const size_t num_bits = ceil(log2(modulus));
        out.allocate(pb);
        quotient.allocate(pb);
        lt_constant.reset(new less_than_constant_gadget<FieldT>(pb, num_bits + 1, out, modulus));
    }

    void generate_r1cs_constraints() {
        this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(quotient * modulus + out, 1, in1 + in2));
        this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(quotient, 1 - pb_linear_combination<FieldT>(quotient), 0));
        // TODO: do we need an additional constraint on the size of out, or is this enough?
        lt_constant->generate_r1cs_constraints();
    }

    void generate_r1cs_witness() {
        unsigned long w1 = this->pb.lc_val(in1).as_ulong();
        unsigned long w2 = this->pb.lc_val(in2).as_ulong();
        assert(ceil(log2(w1)) + ceil(log2(w2)) < 2 * ceil(log2(modulus)));

        this->pb.val(quotient) = (w1 + w2) / modulus;
        this->pb.val(out)      = (w1 + w2) % modulus;

        lt_constant->generate_r1cs_witness();
    }
};

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
}

void LibsnarkProofSystem::ConstrainAddition(const Ciphertext<DCRTPoly>& ctxt1, const Ciphertext<DCRTPoly>& ctxt2,
                                            Ciphertext<DCRTPoly>& ctxt_out) {
    const auto in1 = GetProofMetadata(ctxt1);
    const auto in2 = GetProofMetadata(ctxt2);
    LibsnarkProofMetadata out(ctxt_out->GetElements().size());
    vector<vector<vector<AddModGadget<FieldT>>>> add_mod_gadgets(ctxt_out->GetElements().size());
    for (size_t i = 0; i < 2; i++) {
        const auto c_i     = ctxt_out->GetElements()[i];
        out[i]             = vector<vector<pb_linear_combination<FieldT>>>(c_i.GetNumOfElements());
        add_mod_gadgets[i] = vector<vector<AddModGadget<FieldT>>>(c_i.GetNumOfElements());

        for (size_t j = 0; j < c_i.GetNumOfElements(); j++) {
            const auto c_ij       = c_i.GetElementAtIndex(j);
            const auto& v_ij      = c_ij.GetValues();
            out[i][j]             = vector<pb_linear_combination<FieldT>>(v_ij.GetLength());
            add_mod_gadgets[i][j] = vector<AddModGadget<FieldT>>();
            add_mod_gadgets.reserve(v_ij.GetLength());

            const size_t modulus = c_ij.GetModulus().ConvertToInt();
            for (size_t k = 0; k < v_ij.GetLength(); k++) {
                add_mod_gadgets[i][j].emplace_back(pb, in1->operator[](i)[j][k], in2->operator[](i)[j][k], modulus);
                out[i][j][k] = add_mod_gadgets[i][j][k].out;
                add_mod_gadgets[i][j][k].generate_r1cs_constraints();
                add_mod_gadgets[i][j][k].generate_r1cs_witness();
            }
        }
    }
}

#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
