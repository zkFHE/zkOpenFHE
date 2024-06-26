#ifndef OPENFHE_LIBSNARK_UTILS_H
#define OPENFHE_LIBSNARK_UTILS_H

#include "libsnark/gadgetlib1/gadget.hpp"

template <typename FieldT>
FieldT div(const FieldT& x, const FieldT& y) {
    mpz_t x_mpz, y_mpz, res_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    mpz_init(res_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    mpz_fdiv_q(res_mpz, x_mpz, y_mpz);
    FieldT res((libff::bigint<FieldT::num_limbs>(res_mpz)));
    mpz_clear(x_mpz);
    mpz_clear(y_mpz);
    mpz_clear(res_mpz);
    return res;
}

template <typename FieldT>
FieldT mod(const FieldT& x, const FieldT& y) {
    mpz_t x_mpz, y_mpz, res_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    mpz_init(res_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    mpz_fdiv_r(res_mpz, x_mpz, y_mpz);
    FieldT res((libff::bigint<FieldT::num_limbs>(res_mpz)));
    mpz_clear(x_mpz);
    mpz_clear(y_mpz);
    mpz_clear(res_mpz);
    return res;
}

template <typename FieldT>
bool lt(const FieldT& x, const FieldT& y) {
    mpz_t x_mpz, y_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    bool res = mpz_cmp(x_mpz, y_mpz) < 0;
    mpz_clear(x_mpz);
    mpz_clear(y_mpz);
    return res;
}

template <typename FieldT>
bool lt_eq(const FieldT& x, const FieldT& y) {
    mpz_t x_mpz, y_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    bool res = mpz_cmp(x_mpz, y_mpz) <= 0;
    mpz_clear(x_mpz);
    mpz_clear(y_mpz);
    return res;
}

template <typename FieldT>
bool gt(const FieldT& x, const FieldT& y) {
    mpz_t x_mpz, y_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    bool res = mpz_cmp(x_mpz, y_mpz) > 0;
    mpz_clear(x_mpz);
    mpz_clear(y_mpz);
    return res;
}

template <typename FieldT>
bool gt_eq(const FieldT& x, const FieldT& y) {
    mpz_t x_mpz, y_mpz;
    mpz_init(x_mpz);
    mpz_init(y_mpz);
    x.as_bigint().to_mpz(x_mpz);
    y.as_bigint().to_mpz(y_mpz);
    bool res = mpz_cmp(x_mpz, y_mpz) >= 0;
    mpz_clear(x_mpz);
    mpz_clear(y_mpz);
    return res;
}

#endif  //OPENFHE_LIBSNARK_UTILS_H
