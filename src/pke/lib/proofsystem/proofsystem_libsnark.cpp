#ifndef OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
#define OPENFHE_PROOFSYSTEM_LIBSNARK_CPP

#include "proofsystem/proofsystem_libsnark.h"
#include "libsnark/gadgetlib1/gadget.hpp"
#include "libsnark/gadgetlib2/gadget.hpp"
#include "libsnark/gadgetlib1/gadgets/basic_gadgets.hpp"
#include <vector>

using namespace libsnark;
using std::vector;

template <typename FieldT>
class AddModGadget : public gadget<FieldT> {
public:
    pb_variable<FieldT> quotient;
    pb_variable_array<FieldT> remainder;
    pb_variable_array<FieldT> aux_decomp;

    std::shared_ptr<packing_gadget<FieldT>> packing;
    std::shared_ptr<packing_gadget<FieldT>> packing2;
    size_t modulus;
    pb_variable<FieldT> in1, in2, out, aux;

    AddModGadget(protoboard<FieldT>& pb, const pb_variable<FieldT> in1, const pb_variable<FieldT> in2,
                 const pb_variable<FieldT> out, size_t modulus, const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, annotationPrefix), modulus(modulus), in1(in1), in2(in2), out(out) {
        const size_t num_bits = ceil(log2(modulus));
        quotient.allocate(pb);
        remainder.allocate(pb, num_bits);

        packing.reset(new packing_gadget<FieldT>(pb, remainder, out));
        aux.allocate(pb);
        aux_decomp.allocate(pb, num_bits + 1);
        packing2.reset(new packing_gadget<FieldT>(pb, aux_decomp, aux));
    }

    void generate_r1cs_constraints() {
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(quotient * modulus + out, 1, linear_term<FieldT>(in1) + linear_term<FieldT>(in2)));

        // quotient is boolean
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(quotient, 1 - pb_linear_combination<FieldT>(quotient), FieldT::zero()));

        packing->generate_r1cs_constraints(true);
        packing2->generate_r1cs_constraints(true);
    }

    void generate_r1cs_witness(long int w1, long int w2) {
        assert(ceil(log2(w1)) + ceil(log2(w2)) < 2 * ceil(log2(modulus)));
        this->pb.val(in1)      = w1;
        this->pb.val(in2)      = w2;
        long int w_out         = (w1 + w2) % modulus;
        this->pb.val(quotient) = (w1 + w2) / modulus;
        this->pb.val(out)      = (w1 + w2) % modulus;  // Set out from in
        packing->generate_r1cs_witness_from_packed();
        const size_t num_bits = ceil(log2(modulus));
        this->pb.val(aux)     = FieldT(2) ^ num_bits + w_out - modulus;
        packing2->generate_r1cs_witness_from_packed();
    }
};

void LibsnarkProofSystem::ConstrainAddition(Ciphertext<DCRTPoly> ciphertext) {
    vector<vector<vector<pb_variable<FieldT>>>> in1;  // Get from ciphertext
    vector<vector<vector<pb_variable<FieldT>>>> in2;  // Get from ciphertext
    vector<vector<vector<pb_variable<FieldT>>>> out;
    vector<vector<vector<pb_variable<FieldT>>>> aux;

    vector<vector<vector<AddModGadget<FieldT>>>> add_mod_gadgets;

    out = vector<vector<vector<pb_variable<FieldT>>>>(2);
    for (size_t i = 0; i < 2; i++) {
        const auto c_i     = ciphertext->GetElements()[i];
        out[i]             = vector<vector<pb_variable<FieldT>>>(c_i.GetNumOfElements());
        add_mod_gadgets[i] = vector<vector<AddModGadget<FieldT>>>(c_i.GetNumOfElements());

        for (size_t j = 0; j < c_i.GetNumOfElements();) {
            const auto c_ij       = c_i.GetElementAtIndex(j);
            const auto& v_ij      = c_ij.GetValues();
            out[i][j]             = vector<pb_variable<FieldT>>(v_ij.GetLength());
            add_mod_gadgets[i][j] = vector<AddModGadget<FieldT>>();
            add_mod_gadgets.reserve(v_ij.GetLength());

            const size_t modulus = c_ij.GetModulus().ConvertToInt();
            for (size_t k = 0; k < v_ij.GetLength(); k++) {
                // Allocate out vars
                out[i][j][k] = pb_variable<FieldT>();
                out[i][j][k].allocate(protoboard);
                protoboard.val(out[i][j][k]) = v_ij[k].ConvertToInt<unsigned long>();

                add_mod_gadgets[i][j].emplace_back(
                    protoboard, in1[i][j][k], in2[i][j][k], out[i][j][k], modulus);
                add_mod_gadgets[i][j][k].generate_r1cs_constraints();
                add_mod_gadgets[i][j][k].generate_r1cs_witness(0, 0);
            }
        }
    }
}

#endif  //OPENFHE_PROOFSYSTEM_LIBSNARK_CPP
