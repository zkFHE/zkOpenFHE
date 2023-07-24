#include <gtest/gtest.h>

#include "proofsystem/gadgets_libsnark.h"

using namespace libsnark;

namespace {

TEST(libsnark_openfhe_gadgets, less_than_constant) {
    typedef libff::Fr<libff::default_ec_pp> FieldT;
    libff::default_ec_pp::init_public_params();

    auto expected  = 2 * 2 + 3 * 4 + 1;
    auto test_over = 10;
    for (size_t i = 1; i < expected + test_over; i++) {
        protoboard<FieldT> pb;
        pb_variable<FieldT> a;
        a.allocate(pb, "a");
        pb_variable<FieldT> b;
        b.allocate(pb, "b");
        pb.set_input_sizes(1);

        pb_linear_combination<FieldT> lc;
        lc.assign(pb, 2 * a + 3 * b + 1);

        pb.val(a) = 2;
        pb.val(b) = 4;

        FieldT constant = i;
        // For soundness, we need to set n such that constant < 2^n and lc < 2^n
        size_t n = std::max(1 + constant.as_bigint().num_bits(), 1 + (size_t)ceil(log2(expected + test_over)));
        less_than_constant_gadget<FieldT> g(pb, n, lc, constant);

        g.generate_r1cs_constraints();
        g.generate_r1cs_witness(false);

        EXPECT_EQ(pb.is_satisfied(), i > expected);
    }
}
};  // namespace