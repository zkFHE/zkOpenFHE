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
    pb_linear_combination<FieldT> alpha_packed;
    std::shared_ptr<packing_gadget<FieldT>> pack_alpha;

public:
    const pb_linear_combination<FieldT> A;
    const FieldT B;
    const size_t n;  // A < 2^n, (B-1) < 2^n
    pb_variable<FieldT> less_or_eq;

    // alpha[n] is less_or_eq
    less_than_constant_gadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT>& A, const size_t A_bit_size,
                              const FieldT& B, const std::string& annotation_prefix = "")
        : gadget<FieldT>(pb, FMT(annotation_prefix, "::less_than_constant_gadget")),
          A(A),
          B(B),
          n(std::max(A_bit_size, (B - 1).as_bigint().num_bits())) {
        assert(
            B != 0 &&
            "constraint 'A < 0' cannot be handled by less_than_constant_gadget (and not very meaningful on the modular field), use a custom constraint 'A != 0' instead");

        alpha.allocate(pb, n, FMT(annotation_prefix, "::less_than_constant_gadget::alpha"));
        less_or_eq.allocate(pb, FMT(annotation_prefix, "::less_than_constant_gadget::less_or_eq"));
        alpha.emplace_back(less_or_eq);

        alpha_packed.assign(pb, (FieldT(2) ^ n) + (B - 1) - A);

        pack_alpha.reset(new packing_gadget<FieldT>(pb, alpha, alpha_packed,
                                                    FMT(annotation_prefix, "::less_than_constant_gadget::less_or_eq")));
    };

    void generate_r1cs_constraints();
    void generate_r1cs_witness(bool assert_strict = true);
};

template <typename FieldT>
void less_than_constant_gadget<FieldT>::generate_r1cs_constraints() {
    pack_alpha->generate_r1cs_constraints(true);
    this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, less_or_eq, 1),
                                 FMT(this->annotation_prefix, "::custom_constraint"));
}

template <typename FieldT>
void less_than_constant_gadget<FieldT>::generate_r1cs_witness(bool assert_strict) {
    A.evaluate(this->pb);

    pack_alpha->generate_r1cs_witness_from_packed();

    if (assert_strict) {
        assert((B - 1).as_bigint().num_bits() <= n &&
               "assumption B-1 <= 2^n bits violated in less_than_constant_gadget");
        assert(this->pb.lc_val(A).as_bigint().num_bits() <= n &&
               "assumption A <= 2^n bits violated in less_than_constant_gadget");
        //         TODO: add assert for exact comparison A < B, not only by comparing bit-sizes
        assert(this->pb.lc_val(A).as_bigint().num_bits() <= (B - 1).as_bigint().num_bits() &&
               "less_than_constant constraint does not hold");

        assert(this->pb.val(less_or_eq) == 1 &&
               "less_or_eq bit is not set to 1 with current assignment, constraints will not be satisfied");
    }
}

template <typename FieldT>
FieldT div(FieldT x, FieldT y) {
    mpz_t x_mpz, y_mpz, res_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    mpz_init(res_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    mpz_fdiv_q(res_mpz, x_mpz, y_mpz);
    return FieldT(libff::bigint<FieldT::num_limbs>(res_mpz));
}

template <typename FieldT>
FieldT mod(FieldT x, FieldT y) {
    mpz_t x_mpz, y_mpz, res_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    mpz_init(res_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    mpz_fdiv_r(res_mpz, x_mpz, y_mpz);
    return FieldT(libff::bigint<FieldT::num_limbs>(res_mpz));
}

template <typename FieldT>
class ModGadget : public gadget<FieldT> {
protected:
    std::shared_ptr<less_than_constant_gadget<FieldT>> lt_constant_quotient;
    std::shared_ptr<less_than_constant_gadget<FieldT>> lt_constant_remainder;
    pb_linear_combination<FieldT> in1, in2;
    const size_t in1_bit_size, in2_bit_size, modulus;
    pb_variable<FieldT> quotient;
    FieldT max_quotient_value;

    void init(protoboard<FieldT>& pb, bool assert_strict) {
        const size_t modulus_bit_size = ceil(log2(modulus));

        FieldT max_in_value;
        assert(!(in1.is_constant() && in2.is_constant()) &&
               "trying to instantiate mod-reduction gadget with constant input, which is unnecessary");
        // Detailed accounting saves us one bit of estimation for the common case where either in1 or in2 is the constant 1
        FieldT in1_max_value = ((FieldT(2) ^ (in1_bit_size)) - 1);
        FieldT in2_max_value = ((FieldT(2) ^ (in2_bit_size)) - 1);
        if (in1.is_constant()) {
            assert(in2_bit_size + in1.constant_term().as_bigint().num_bits() < FieldT::num_bits);
            max_in_value = (in2_max_value * in1.constant_term());
        }
        else if (in2.is_constant()) {
            assert(in1_bit_size + in2.constant_term().as_bigint().num_bits() < FieldT::num_bits);
            max_in_value = (in1_max_value * in2.constant_term());
        }
        else {
            assert(in1_bit_size + in2_bit_size < FieldT::num_bits);
            max_in_value = (in1_max_value * in2_max_value);
        }

        assert(
            max_in_value.as_bigint().num_bits() >= modulus_bit_size &&
            "unnecessary mod reduction gadget");  // Needed, as otherwise we cannot instantiate `lt_constant_quotient` gadget with `max_quotient_value` == 0

        // max_quotient_value does not have to be a very tight upper bound for soundness, we just need to ensure that quotient * modulus does not overflow the field modulus
        // However, we want max_quotient to be a tight upper bound for efficiency, in order to reduce the number of constraints needed for the range check
        max_quotient_value = div(max_in_value, FieldT(modulus));

        quotient.allocate(pb, FMT(this->annotation_prefix, "::quotient"));
        // a, b < modulus ==> a*b = quotient * modulus + out and quotient < modulus
        // quotient < 2^(1+quotient_bit_size) and out < 2^(1+modulus_bit_size)
        lt_constant_quotient.reset(new less_than_constant_gadget<FieldT>(
            pb, quotient, (max_quotient_value + 1).as_bigint().num_bits(), max_quotient_value + 1,
            FMT(this->annotation_prefix, "::lt_constant_quotient")));
        lt_constant_remainder.reset(new less_than_constant_gadget<FieldT>(
            pb, out, modulus_bit_size, modulus, FMT(this->annotation_prefix, "::lt_constant_remainder")));
    }

    ModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1, const size_t in1_bit_size,
              const pb_linear_combination<FieldT> in2, const size_t in2_bit_size, size_t modulus,
              const pb_variable<FieldT> out, const std::string& annotationPrefix = "", bool assert_strict = true)
        : gadget<FieldT>(pb, annotationPrefix),
          modulus(modulus),
          in1(in1),
          in1_bit_size(in1_bit_size),
          in2(in2),
          in2_bit_size(in2_bit_size),
          out(out) {
        init(pb, in1_bit_size, in2_bit_size, assert_strict);
    }

    ModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1, const size_t in1_bit_size,
              const pb_linear_combination<FieldT> in2, const size_t in2_bit_size, size_t modulus,
              const std::string& annotationPrefix = "", bool assert_strict = true)
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::mod_gadget")),
          modulus(modulus),
          in1(in1),
          in1_bit_size(in1_bit_size),
          in2(in2),
          in2_bit_size(in2_bit_size) {
        out.allocate(pb, FMT(this->annotation_prefix, "::out"));
        init(pb, assert_strict);
    }

    ModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in, const size_t in_bit_size, size_t modulus,
              const pb_variable<FieldT> out, const std::string& annotationPrefix = "", bool assert_strict = true)
        : gadget<FieldT>(pb, annotationPrefix), modulus(modulus), in1(in), in1_bit_size(in_bit_size), out(out) {
        in2.assign(pb, FieldT(1));
        in2_bit_size = 1;
        init(pb, assert_strict);
    }

public:
    pb_variable<FieldT> out;

    ModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in, const size_t in_bit_size, size_t modulus,
              const std::string& annotationPrefix = "", bool assert_strict = true)
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::mod_gadget")),
          modulus(modulus),
          in1(in),
          in1_bit_size(in_bit_size) {
        out.allocate(pb, FMT(this->annotation_prefix, "::out"));
        in2.assign(pb, FieldT(1));
        in2_bit_size = 1;
        init(pb, assert_strict);
    }

    void generate_r1cs_constraints() {
        this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(in1, in2, quotient * modulus + out),
                                     FMT(this->annotation_prefix, "::in1*in2=quotient*modulus+out"));
        lt_constant_quotient->generate_r1cs_constraints();
        lt_constant_remainder->generate_r1cs_constraints();
    }

    void generate_r1cs_witness() {
        in1.evaluate(this->pb);
        in2.evaluate(this->pb);

        assert(this->pb.lc_val(in1).as_bigint().num_bits() <= in1_bit_size);
        assert(this->pb.lc_val(in2).as_bigint().num_bits() <= in2_bit_size);

        this->pb.val(quotient) = div(this->pb.lc_val(in1) * this->pb.lc_val(in2), FieldT(modulus));
        this->pb.val(out)      = mod(this->pb.lc_val(in1) * this->pb.lc_val(in2), FieldT(modulus));

        assert(this->pb.val(quotient).as_bigint().num_bits() <= max_quotient_value.as_bigint().num_bits());
        assert(this->pb.val(out).as_bigint().num_bits() <= (size_t)ceil(log2(modulus)));

        lt_constant_quotient->generate_r1cs_witness();
        lt_constant_remainder->generate_r1cs_witness();
    }
};

template <typename FieldT>
class ModAssignGadget : public ModGadget<FieldT> {
public:
    ModAssignGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in, const size_t in_bit_size,
                    size_t modulus, const pb_variable<FieldT> out, const std::string& annotationPrefix = "")
        : ModGadget<FieldT>(pb, in, in_bit_size, modulus, out, FMT(annotationPrefix, "::mod_assign")) {}
};

template <typename FieldT>
class AddModGadget : public ModGadget<FieldT> {
protected:
    inline pb_linear_combination<FieldT> add(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1,
                                             const pb_linear_combination<FieldT> in2) {
        pb_linear_combination<FieldT> lc;
        lc.assign(pb, in1 + in2);
        return lc;
    }

public:
    AddModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1, const size_t in1_bit_size,
                 const pb_linear_combination<FieldT> in2, const size_t in2_bit_size, size_t modulus,
                 const std::string& annotationPrefix = "")
        : ModGadget<FieldT>(pb, add(pb, in1, in2), std::max(in1_bit_size, in2_bit_size) + 1, modulus,
                            FMT(annotationPrefix, "add_mod")) {}
    AddModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in, size_t modulus,
                 const std::string& annotationPrefix = "") = delete;
};

template <typename FieldT>
class SubModGadget : public ModGadget<FieldT> {
protected:
    inline pb_linear_combination<FieldT> sub(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1,
                                             const pb_linear_combination<FieldT> in2, const size_t modulus) {
        pb_linear_combination<FieldT> lc;
        lc.assign(pb, in1 + FieldT(modulus) - in2);
        return lc;
    }

public:
    SubModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1, const size_t in1_bit_size,
                 const pb_linear_combination<FieldT> in2, const size_t in2_bit_size, size_t modulus,
                 const std::string& annotationPrefix = "")
        : ModGadget<FieldT>(pb, sub(pb, in1, in2, modulus), std::max(in1_bit_size, (size_t)ceil(log2(modulus))) + 1,
                            modulus, FMT(annotationPrefix, "sub_mod")) {
        assert(in2_bit_size < (size_t)ceil(log2(modulus)));
    }
    SubModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in, size_t modulus,
                 const std::string& annotationPrefix = "") = delete;
};

template <typename FieldT>
class MulModGadget : public ModGadget<FieldT> {
public:
    MulModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1, const size_t in1_bit_size,
                 const pb_linear_combination<FieldT> in2, const size_t in2_bit_size, size_t modulus,
                 const std::string& annotationPrefix = "")
        : ModGadget<FieldT>(pb, in1, in1_bit_size, in2, in2_bit_size, modulus, FMT(annotationPrefix, "mul_mod")) {}
    MulModGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in, size_t modulus,
                 const std::string& annotationPrefix = "") = delete;
};

template <typename FieldT>
class MulGadget : public gadget<FieldT> {
public:
    pb_linear_combination<FieldT> in1, in2;
    pb_linear_combination<FieldT> out;
    pb_variable<FieldT> tmp;

    MulGadget(protoboard<FieldT>& pb, const pb_linear_combination<FieldT> in1, const pb_linear_combination<FieldT> in2,
              const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, annotationPrefix), in1(in1), in2(in2) {
        assert(!(in1.is_constant() && in2.is_constant()) && "unnecessary MulGadget if both inputs are constants");
        if (in1.is_constant()) {
            out.assign(pb, in1.constant_term() * in2);
        }
        else if (in2.is_constant()) {
            out.assign(pb, in1 * in2.constant_term());
        }
        else {
            tmp.allocate(pb, FMT(this->annotation_prefix, "::tmp"));
            out.assign(pb, tmp);
        }
    }

    void generate_r1cs_constraints() {
        if (!in1.is_constant() && !in2.is_constant()) {
            this->pb.add_r1cs_constraint(r1cs_constraint<FieldT>(in1, in2, out),
                                         FMT(this->annotation_prefix, "::mul_constraint"));
        }
    }

    void generate_r1cs_witness() {
        if (!in1.is_constant() && !in2.is_constant()) {
            in1.evaluate(this->pb);
            in2.evaluate(this->pb);
            this->pb.val(tmp) = this->pb.lc_val(in1) * this->pb.lc_val(in2);
        }
    }
};

template <typename FieldT, typename Gadget>
class BatchGadget : gadget<FieldT> {
public:
    vector<Gadget> gadgets;

    BatchGadget(protoboard<FieldT>& pb, const vector<pb_linear_combination<FieldT>>& in, const size_t in_bit_size,
                const size_t& modulus, const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::batch_gadget")) {
        gadgets.reserve(in.size());
        for (size_t i = 0; i < in.size(); ++i) {
            gadgets.emplace_back(pb, in[i], in_bit_size, modulus,
                                 FMT(this->annotation_prefix, ("[" + std::to_string(i) + "]").c_str()));
        }
    }

    BatchGadget(protoboard<FieldT>& pb, const vector<pb_linear_combination<FieldT>>& in, const size_t in_bit_size,
                const size_t& modulus, const vector<pb_variable<FieldT>>& out, const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::batch_gadget")) {
        assert(in.size() == out.size());
        gadgets.reserve(in.size());
        for (size_t i = 0; i < in.size(); ++i) {
            gadgets.emplace_back(pb, in[i], in_bit_size, modulus, out[i],
                                 FMT(this->annotation_prefix, ("[" + std::to_string(i) + "]").c_str()));
        }
    }

    BatchGadget(protoboard<FieldT>& pb, const vector<pb_linear_combination<FieldT>>& in1,
                const vector<pb_linear_combination<FieldT>>& in2, const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::BatchGadget")) {
        assert(in1.size() == in2.size());
        gadgets.reserve(in1.size());
        for (size_t i = 0; i < in1.size(); ++i) {
            gadgets.emplace_back(pb, in1[i], in2[i],
                                 FMT(this->annotation_prefix, ("[" + std::to_string(i) + "]").c_str()));
        }
    }

    BatchGadget(protoboard<FieldT>& pb, const vector<pb_linear_combination<FieldT>>& in1, const size_t in1_bit_size,
                const vector<pb_linear_combination<FieldT>>& in2, const size_t in2_bit_size, const size_t& modulus,
                const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::BatchGadget")) {
        assert(in1.size() == in2.size());
        gadgets.reserve(in1.size());
        for (size_t i = 0; i < in1.size(); ++i) {
            gadgets.emplace_back(pb, in1[i], in1_bit_size, in2[i], in2_bit_size, modulus,
                                 FMT(this->annotation_prefix, ("[" + std::to_string(i) + "]").c_str()));
        }
    }

    void generate_r1cs_constraints() {
        for (auto& g_i : gadgets) {
            g_i.generate_r1cs_constraints();
        }
    }

    void generate_r1cs_witness() {
        for (auto& g_i : gadgets) {
            g_i.generate_r1cs_witness();
        }
    }

    vector<pb_linear_combination<FieldT>> get_output() {
        vector<pb_linear_combination<FieldT>> out(gadgets.size());
        for (size_t i = 0; i < gadgets.size(); ++i) {
            out[i] = gadgets[i].out;
        }
        return out;
    }

    vector<pb_variable<FieldT>> get_output_vars() {
        vector<pb_variable<FieldT>> out(gadgets.size());
        for (size_t i = 0; i < gadgets.size(); ++i) {
            out[i] = gadgets[i].out;
        }
        return out;
    }
};

template <typename FieldT, typename Gadget>
class DoubleBatchGadget : gadget<FieldT> {
public:
    vector<vector<Gadget>> gadgets;

    DoubleBatchGadget(protoboard<FieldT>& pb, const vector<vector<pb_linear_combination<FieldT>>>& in1,
                      const vector<vector<pb_linear_combination<FieldT>>>& in2, const vector<size_t>& modulus,
                      const std::string& annotationPrefix = "")
        : gadget<FieldT>(pb, FMT(annotationPrefix, "::DoubleBatchGadget")) {
        assert(in1.size() == in2.size());
        assert(in1.size() == modulus.size());
        gadgets.reserve(in1.size());
        for (size_t i = 0; i < in1.size(); ++i) {
            assert(in1[i].size() == in2[i].size());
            gadgets.push_back(vector<Gadget>());
            gadgets[i].reserve(in1[i].size());

            for (size_t j = 0; j < in1[i].size(); ++j) {
                gadgets[i].emplace_back(
                    pb, in1[i][j], in2[i][j], modulus[i],
                    FMT(this->annotation_prefix, ("[" + std::to_string(i) + "][" + std::to_string(j) + "]").c_str()));
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
