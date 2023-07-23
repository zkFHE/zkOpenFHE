#ifndef OPENFHE_GADGETS_LIBSNARK_H
#define OPENFHE_GADGETS_LIBSNARK_H
#include "proofsystem/gadgets_libsnark.h"
#include "libsnark/gadgetlib1/gadget.hpp"
#include "libsnark/gadgetlib2/gadget.hpp"
#include "libsnark/gadgetlib1/gadgets/basic_gadgets.hpp"
#include <vector>
#include <cassert>

#define LIBSNARK_PROOF_METADATA_KEY "libsnark_proof_metadata"

using namespace libsnark;
using std::cout, std::endl;
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
        assert(std::max(this->pb.lc_val(in1).as_bigint().num_bits(), this->pb.lc_val(in2).as_bigint().num_bits()) <
               modulus);
        unsigned long w1 = this->pb.lc_val(in1).as_ulong();
        unsigned long w2 = this->pb.lc_val(in2).as_ulong();

        this->pb.val(quotient) = (w1 + w2) / modulus;
        this->pb.val(out)      = (w1 + w2) % modulus;

        lt_constant->generate_r1cs_witness();
    }
};

template <typename FieldT>
class MulModGadget : public gadget<FieldT> {
public:
    std::shared_ptr<less_than_constant_gadget<FieldT>> lt_constant_quotient;
    std::shared_ptr<less_than_constant_gadget<FieldT>> lt_constant_remainder;
    size_t modulus;
    pb_linear_combination<FieldT> in1, in2;
    pb_variable<FieldT> out, quotient;

    MulModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1,
                 const pb_linear_combination<FieldT> in2, size_t modulus, const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, annotationPrefix), modulus(modulus), in1(in1), in2(in2) {
        const size_t num_bits = ceil(log2(modulus));
        out.allocate(pb);
        quotient.allocate(pb);
        // a, b < modulus ==> a*b = quotient * modulus + out and quotient < modulus
        lt_constant_quotient.reset(new less_than_constant_gadget<FieldT>(pb, num_bits + 1, quotient, modulus));
        lt_constant_remainder.reset(new less_than_constant_gadget<FieldT>(pb, num_bits + 1, out, modulus));
    }

    void generate_r1cs_constraints() {
        this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(quotient * modulus + out, 1, in1 + in2));
        // TODO: do we need an additional constraint on the size of out, or is this enough?
        lt_constant_quotient->generate_r1cs_constraints();
        lt_constant_remainder->generate_r1cs_constraints();
    }

    void generate_r1cs_witness() {
        unsigned long w1 = this->pb.lc_val(in1).as_ulong();
        unsigned long w2 = this->pb.lc_val(in2).as_ulong();
        assert(this->pb.lc_val(in1).as_bigint().num_bits() + this->pb.lc_val(in2).as_bigint().num_bits() <=
               2 * ceil(log2(modulus)));

        this->pb.val(quotient) = (w1 * w2) / modulus;
        this->pb.val(out)      = (w1 * w2) % modulus;

        lt_constant_quotient->generate_r1cs_witness();
        lt_constant_remainder->generate_r1cs_witness();
    }
};

template <typename FieldT, typename Gadget>
class BatchGadget : gadget<FieldT> {
public:
    vector<vector<Gadget>> gadgets;

    BatchGadget(protoboard<FieldT>& pb, const vector<vector<pb_linear_combination<FieldT>>>& in1,
                const vector<vector<pb_linear_combination<FieldT>>>& in2, const vector<size_t>& modulus,
                const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, annotationPrefix) {
        assert(in1.size() == in2.size());
        assert(in1.size() == modulus.size());
        gadgets.reserve(in1.size());
        for (size_t i = 0; i < in1.size(); ++i) {
            assert(in1[i].size() == in2[i].size());
            gadgets.push_back(vector<Gadget>());
            gadgets[i].reserve(in1[i].size());

            for (size_t j = 0; j < in1[i].size(); ++j) {
                gadgets[i].emplace_back(pb, in1[i][j], in2[i][j], modulus[i]);
            }
        }
    }

    void generate_r1cs_constraints() {
        for (auto& g_i : gadgets) {
            for (auto& g_ij : g_i) {
                g_ij.generate_r1cs_constraints();
            }
        }
    }

    void generate_r1cs_witness() {
        for (auto& g_i : gadgets) {
            for (auto& g_ij : g_i) {
                g_ij.generate_r1cs_witness();
            }
        }
    }

    vector<vector<pb_linear_combination<FieldT>>> get_output() {
        vector<vector<pb_linear_combination<FieldT>>> out(gadgets.size());
        for (size_t i = 0; i < gadgets.size(); ++i) {
            out[i] = vector<pb_linear_combination<FieldT>>(gadgets[i].size());
            for (size_t j = 0; j < gadgets[i].size(); ++j) {
                out[i][j] = gadgets[i][j].out;
            }
        }
        return out;
    }
};

#endif  //OPENFHE_GADGETS_LIBSNARK_H
