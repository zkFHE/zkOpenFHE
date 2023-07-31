#define PROOFSYSTEM_CHECK_STRICT

#define PROOFSYSTEM_ASSERT_EQ(a, b) assert(a == b);

#ifdef PROOFSYSTEM_CHECK_STRICT
    #define PROOFSYSTEM_ASSERT_EQ(a, b)                \
        do {                                           \
            if (a != b) {                              \
                std::cerr << a << " != " << b << endl; \
            }                                          \
            assert(a == b);                            \
        } while (0);
#else
    #define PROOFSYSTEM_ASSERT_EQ(a, b) ;
#endif

#include <gtest/gtest.h>

#include "proofsystem/gadgets_libsnark.h"
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "openfhe.h"
#include "proofsystem/proofsystem_libsnark.cpp"  // TODO: fix this ugly hack after the deadline, at the moment the build system throws a weird linker error without this hack
#include "proofsystem/proofsystem_libsnark.h"

namespace {
typedef libff::Fr<libff::default_ec_pp> FieldT;

TEST(libsnark_openfhe_gadgets, less_than_constant) {
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
        less_than_constant_gadget<FieldT> g(pb, lc, ceil(log2(expected)), constant);

        g.generate_r1cs_constraints();
        g.generate_r1cs_witness(false);

        EXPECT_EQ(pb.is_satisfied(), i > expected);
    }
}

TEST(libsnark_openfhe_gadgets, mod_gadget) {
    libff::default_ec_pp::init_public_params();

    vector<size_t> moduli = {2, (1ul << 2) - 1, (1ul << 10) - 1};
    for (const auto& modulus : moduli) {
        size_t q = 42;
        for (size_t i = 0; i < modulus; i++) {
            protoboard<FieldT> pb;
            pb_variable<FieldT> a;
            a.allocate(pb, "a");
            pb.set_input_sizes(1);

            FieldT val = FieldT(q) * FieldT(modulus) + i;
            q++;
            pb.val(a) = val;
            ModGadget<FieldT> g(pb, a, FieldT(q) * FieldT(modulus) + modulus - 1, modulus);
            g.generate_r1cs_constraints();
            g.generate_r1cs_witness();
            EXPECT_EQ(pb.is_satisfied(), true);
            EXPECT_EQ(pb.val(g.out), i);
        }
    }
}

TEST(libsnark_openfhe_gadgets, ntt) {
    libff::default_ec_pp::init_public_params();

    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(1);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs
    parameters.SetKeySwitchTechnique(KeySwitchTechnique::BV);
    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);

    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    KeyPair<DCRTPoly> keyPair;
    keyPair              = cryptoContext->KeyGen();
    Plaintext plaintext1 = cryptoContext->MakePackedPlaintext({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12});

    auto ctxt = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);

    using VecType = typename DCRTPoly::PolyType::Vector;
    auto in_0     = ctxt->GetElements()[0].GetElementAtIndex(0);
    in_0.SwitchFormat();
    assert(in_0.GetFormat() == Format::COEFFICIENT);
    auto out_0(in_0);
    out_0.SwitchFormat();
    assert(out_0.GetFormat() == Format::EVALUATION);

    // out.GetRootOfUnity() is set to 0, as is out.GetParams().GetRootOfUnity()
    auto rootOfUnity = out_0.GetRootOfUnity();
    auto CycloOrder  = out_0.GetCyclotomicOrder();

    LibsnarkProofSystem ps(cryptoContext);
    ps.ConstrainPublicInput(ctxt);
    const auto& modulus = in_0.GetModulus();
    auto in_0_0         = in_0.GetValues();
    auto out_0_0        = out_0.GetValues();
    usint CycloOrderHf  = (CycloOrder >> 1);

    using namespace intnat;
    auto crt       = ChineseRemainderTransformFTTNat<VecType>();
    auto mapSearch = crt.m_rootOfUnityReverseTableByModulus.find(modulus);
    if (mapSearch == crt.m_rootOfUnityReverseTableByModulus.end() || mapSearch->second.GetLength() != CycloOrderHf) {
        crt.PreCompute(rootOfUnity, CycloOrder, modulus);
    }

    auto in_lc        = (*LibsnarkProofSystem::GetProofMetadata(ctxt))[0][0];
    auto in_max_value = (*LibsnarkProofSystem::GetProofMetadata(ctxt)).max_value[0][0];
    for (size_t i = 0; i < in_0_0.GetLength(); ++i) {
        ps.pb.lc_val(in_lc[i]) = FieldT(in_0_0[i].Mod(modulus).ConvertToInt());
    }
    vector<pb_linear_combination<FieldT>> out_lc;
    FieldT out_max_value;

    ps.ConstrainNTT(ChineseRemainderTransformFTTNat<VecType>::m_rootOfUnityReverseTableByModulus[modulus],
                    ChineseRemainderTransformFTTNat<VecType>::m_rootOfUnityPreconReverseTableByModulus[modulus], in_0_0,
                    out_0_0, in_lc, in_max_value, out_lc, out_max_value);

    auto pb = ps.pb;
    EXPECT_EQ(pb.is_satisfied(), true);

    FieldT q(modulus.template ConvertToInt<unsigned long>());
    for (size_t i = 0; i < out_0_0.GetLength(); ++i) {
        out_lc[i].evaluate(pb);
        EXPECT_EQ(mod(pb.lc_val(out_lc[i]), q), FieldT(out_0_0[i].ConvertToInt()));
    }
}

TEST(libsnark_openfhe_gadgets, intt) {
    libff::default_ec_pp::init_public_params();

    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(1);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs
    parameters.SetKeySwitchTechnique(KeySwitchTechnique::BV);
    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);

    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    KeyPair<DCRTPoly> keyPair;
    keyPair              = cryptoContext->KeyGen();
    Plaintext plaintext1 = cryptoContext->MakePackedPlaintext({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12});

    auto ctxt = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);

    using VecType = typename DCRTPoly::PolyType::Vector;
    auto in_0     = ctxt->GetElements()[0].GetElementAtIndex(0);
    auto out_0(in_0);
    assert(in_0.GetFormat() == Format::EVALUATION);
    out_0.SwitchFormat();

    // out.GetRootOfUnity() is set to 0, as is out.GetParams().GetRootOfUnity()
    auto rootOfUnity = out_0.GetRootOfUnity();
    auto CycloOrder  = out_0.GetCyclotomicOrder();

    LibsnarkProofSystem ps(cryptoContext);
    ps.ConstrainPublicInput(ctxt);
    const auto& modulus = in_0.GetModulus();
    auto in_0_0         = in_0.GetValues();
    auto out_0_0        = out_0.GetValues();
    usint CycloOrderHf  = (CycloOrder >> 1);

    using namespace intnat;
    auto crt       = ChineseRemainderTransformFTTNat<VecType>();
    auto mapSearch = ChineseRemainderTransformFTTNat<VecType>::m_rootOfUnityReverseTableByModulus.find(modulus);
    if (mapSearch == ChineseRemainderTransformFTTNat<VecType>::m_rootOfUnityReverseTableByModulus.end() ||
        mapSearch->second.GetLength() != CycloOrderHf) {
        crt.PreCompute(rootOfUnity, CycloOrder, modulus);
    }

    usint msb = lbcrypto::GetMSB64(CycloOrderHf - 1);

    auto in_lc        = (*LibsnarkProofSystem::GetProofMetadata(ctxt))[0][0];
    auto in_max_value = (*LibsnarkProofSystem::GetProofMetadata(ctxt)).max_value[0][0];
    for (size_t i = 0; i < out_0_0.GetLength(); ++i) {
        assert(ps.pb.lc_val(in_lc[i]) == FieldT(in_0_0[i].Mod(modulus).ConvertToInt()));
    }
    vector<pb_linear_combination<FieldT>> out_lc;
    FieldT out_max_value;

    ps.ConstrainINTT(ChineseRemainderTransformFTTNat<VecType>::m_rootOfUnityInverseReverseTableByModulus[modulus],
                     ChineseRemainderTransformFTTNat<VecType>::m_rootOfUnityInversePreconReverseTableByModulus[modulus],
                     ChineseRemainderTransformFTTNat<VecType>::m_cycloOrderInverseTableByModulus[modulus][msb],
                     ChineseRemainderTransformFTTNat<VecType>::m_cycloOrderInversePreconTableByModulus[modulus][msb],
                     in_0_0, out_0_0, in_lc, in_max_value, out_lc, out_max_value);

    auto pb = ps.pb;
    EXPECT_EQ(pb.is_satisfied(), true);

    FieldT q(modulus.template ConvertToInt<unsigned long>());
    for (size_t i = 0; i < out_0_0.GetLength(); ++i) {
        out_lc[i].evaluate(pb);
        EXPECT_EQ(mod(pb.lc_val(out_lc[i]), q), FieldT(out_0_0[i].ConvertToInt()));
    }

    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
}

TEST(libsnark_openfhe_gadgets, set_format) {
    libff::default_ec_pp::init_public_params();

    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(1);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs
    parameters.SetKeySwitchTechnique(KeySwitchTechnique::BV);
    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);

    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    KeyPair<DCRTPoly> keyPair;
    keyPair              = cryptoContext->KeyGen();
    Plaintext plaintext1 = cryptoContext->MakePackedPlaintext({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12});

    auto ctxt = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);

    auto in = ctxt->GetElements()[0].GetElementAtIndex(0);
    auto out(in);
    assert(out.GetFormat() == Format::EVALUATION);
    out.SetFormat(Format::COEFFICIENT);

    LibsnarkProofSystem ps(cryptoContext);
    ps.ConstrainPublicInput(ctxt);
    LibsnarkProofMetadata in_metadata = *LibsnarkProofSystem::GetProofMetadata(ctxt);

    auto in_lc          = in_metadata[0][0];
    FieldT in_max_value = in_metadata.max_value[0][0];

    vector<pb_linear_combination<FieldT>> out_lc;
    FieldT out_max_value;

    ps.ConstrainSetFormat(Format::COEFFICIENT, in, out, in_lc, in_max_value, out_lc, out_max_value);

    auto q  = FieldT(in.GetModulus().template ConvertToInt<unsigned long>());
    auto pb = ps.pb;
    EXPECT_EQ(pb.is_satisfied(), true);
    for (size_t i = 0; i < out.GetLength(); ++i) {
        out_lc[i].evaluate(pb);
        EXPECT_EQ(mod(pb.lc_val(out_lc[i]), q), FieldT(out[i].ConvertToInt()));
    }
    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
}

TEST(libsnark_openfhe_gadgets, switch_modulus) {
    libff::default_ec_pp::init_public_params();

    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(1);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs
    parameters.SetKeySwitchTechnique(KeySwitchTechnique::BV);
    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);

    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    KeyPair<DCRTPoly> keyPair;
    keyPair              = cryptoContext->KeyGen();
    Plaintext plaintext1 = cryptoContext->MakePackedPlaintext({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12});

    auto ctxt = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);

    auto in = ctxt->GetElements()[0];
    in.SetFormat(Format::COEFFICIENT);
    auto out(in);

    //    using VecType = typename DCRTPolyImpl<DCRTPoly>::PolyType::Vector;
    auto in_0  = in.GetElementAtIndex(0);
    auto in_1  = in.GetElementAtIndex(1);
    auto out_0 = out.GetElementAtIndex(0);

    auto newModulus     = in_1.GetModulus();
    auto newRootOfunity = in_0.GetRootOfUnity();
    out_0.SwitchModulus(newModulus, newRootOfunity, 0, 0);

    LibsnarkProofSystem ps(cryptoContext);
    ps.ConstrainPublicInput(ctxt);
    LibsnarkProofMetadata in_metadata = *LibsnarkProofSystem::GetProofMetadata(ctxt);

    auto in_lc        = in_metadata[0][0];
    auto in_max_value = in_metadata.max_value[0][0];
    vector<pb_linear_combination<FieldT>> out_lc;
    FieldT out_max_value;
    for (int i = 0; i < in_0.GetLength(); i++) {
        ps.pb.lc_val(in_metadata[0][0][i]) = FieldT(in_0[i].template ConvertToInt<unsigned long>());
    }
    ps.ConstrainSwitchModulus(newModulus, newRootOfunity, 0, 0, in_0, out_0, in_lc, in_max_value, out_lc,
                              out_max_value);

    auto pb = ps.pb;

    EXPECT_EQ(pb.is_satisfied(), true);

    for (size_t i = 0; i < out_0.GetLength(); ++i) {
        out_lc[i].evaluate(pb);
        EXPECT_EQ(pb.lc_val(out_lc[i]), FieldT(out_0[i].ConvertToInt()));
    }
    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
}

TEST(libsnark_openfhe_gadgets, key_switch_precompute_core) {
    libff::default_ec_pp::init_public_params();

    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(1);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs
    parameters.SetKeySwitchTechnique(KeySwitchTechnique::BV);
    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);

    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    KeyPair<DCRTPoly> keyPair;
    keyPair              = cryptoContext->KeyGen();
    Plaintext plaintext1 = cryptoContext->MakePackedPlaintext({1, 0, 1, 0});

    auto ctxt = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);
    cryptoContext->ModReduceInPlace(ctxt);  // Reduce number of levels to make test faster

    const DCRTPoly in = ctxt->GetElements()[0];
    const std::shared_ptr<vector<DCRTPoly>> out =
        KeySwitchBV().EvalKeySwitchPrecomputeCore(in, cryptoContext->GetCryptoParameters());

    LibsnarkProofSystem ps(cryptoContext);
    ps.ConstrainPublicInput(ctxt);
    LibsnarkProofMetadata in_metadata = *LibsnarkProofSystem::GetProofMetadata(ctxt);

    const auto in_lc        = in_metadata[0];
    const auto in_max_value = in_metadata.max_value[0];
    vector<vector<vector<pb_linear_combination<FieldT>>>> out_lc;
    vector<vector<FieldT>> out_max_value;

    cout << "in.GetNumOfElements() = " << in.GetNumOfElements() << endl;
    ps.ConstrainKeySwitchPrecomputeCore(in, cryptoContext->GetCryptoParameters(), out, in_lc, in_max_value, out_lc,
                                        out_max_value);

    auto pb = ps.pb;

    EXPECT_EQ(pb.is_satisfied(), true);

    auto q = FieldT(in.GetModulus().template ConvertToInt<unsigned long>());
    for (size_t i = 0; i < out_lc.size(); ++i) {
        for (size_t j = 0; j < out_lc[i].size(); ++j) {
            for (size_t k = 0; k < out_lc[j].size(); ++k) {
                out_lc[i][j][k].evaluate(pb);
                auto expected = (*out)[i].GetElementAtIndex(j).GetValues()[k];
                EXPECT_EQ(mod(pb.lc_val(out_lc[i][j][k]), q), FieldT(expected.ConvertToInt()));
            }
        }
    }
    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
}

TEST(libsnark_openfhe_gadgets, key_switch_fast_key_switch_core) {
    libff::default_ec_pp::init_public_params();

    CCParams<CryptoContextBGVRNS> parameters;
    parameters.SetMultiplicativeDepth(2);
    parameters.SetPlaintextModulus(65537);
    parameters.SetScalingTechnique(FIXEDMANUAL);
    // use BV instead of HYBRID, as it is a lot simpler to arithmetize, even if it requires a quadratic number of NTTs
    parameters.SetKeySwitchTechnique(KeySwitchTechnique::BV);
    CryptoContext<DCRTPoly> cryptoContext = GenCryptoContext(parameters);

    cryptoContext->Enable(PKE);
    cryptoContext->Enable(KEYSWITCH);
    cryptoContext->Enable(LEVELEDSHE);

    KeyPair<DCRTPoly> keyPair;
    keyPair = cryptoContext->KeyGen();
    cryptoContext->EvalMultKeyGen(keyPair.secretKey);
    Plaintext plaintext1 = cryptoContext->MakePackedPlaintext({1, 0, 1, 0});

    auto ctxt = cryptoContext->Encrypt(keyPair.publicKey, plaintext1);
    ctxt      = cryptoContext->EvalMultNoRelin(ctxt, cryptoContext->Encrypt(keyPair.publicKey, plaintext1));

    const DCRTPoly in = ctxt->GetElements()[0];
    const std::shared_ptr<vector<DCRTPoly>> digits =
        KeySwitchBV().EvalKeySwitchPrecomputeCore(in, cryptoContext->GetCryptoParameters());

    const auto evalKeyVec = cryptoContext->GetEvalMultKeyVector(ctxt->GetKeyTag());
    auto evk              = evalKeyVec[0];
    auto paramsQl         = in.GetParams();
    auto out              = KeySwitchBV().EvalFastKeySwitchCore(digits, evk, paramsQl);

    LibsnarkProofSystem ps(cryptoContext);
    //    ps.ConstrainPublicInput(ctxt);
    //    LibsnarkProofMetadata in_metadata = *LibsnarkProofSystem::GetProofMetadata(ctxt);

    vector<vector<vector<pb_linear_combination<FieldT>>>> in_lc((*digits).size());
    vector<vector<FieldT>> in_max_value((*digits).size());
    for (size_t i = 0; i < in_lc.size(); ++i) {
        in_lc[i].resize((*digits)[i].GetNumOfElements());
        in_max_value[i].resize((*digits)[i].GetNumOfElements());
        for (size_t j = 0; j < in_lc[i].size(); ++j) {
            in_max_value[i][j] = FieldT((*digits)[i].GetElementAtIndex(j).GetModulus().ConvertToInt());
            in_lc[i][j].resize((*digits)[i].GetElementAtIndex(j).GetValues().GetLength());
            for (size_t k = 0; k < in_lc[i][j].size(); ++k) {
                pb_variable<FieldT> x;
                x.allocate(ps.pb);
                ps.pb.val(x) = FieldT((*digits)[i].GetElementAtIndex(j).GetValues()[k].ConvertToInt());
                in_lc[i][j][k].assign(ps.pb, x);
            }
        }
    }
    vector<vector<vector<pb_linear_combination<FieldT>>>> out_lc;
    vector<vector<FieldT>> out_max_value;

    cout << "in.GetNumOfElements() = " << in.GetNumOfElements() << endl;
    ps.ConstrainFastKeySwitchCore(digits, evk, paramsQl, out, in_lc, in_max_value, out_lc, out_max_value);

    auto pb = ps.pb;

    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;

    EXPECT_EQ(pb.is_satisfied(), true);

    for (size_t i = 0; i < out_lc.size(); ++i) {
        for (size_t j = 0; j < out_lc[i].size(); ++j) {
            auto q = FieldT((*out)[i].GetElementAtIndex(j).GetModulus().template ConvertToInt<unsigned long>());
            for (size_t k = 0; k < out_lc[j].size(); ++k) {
                out_lc[i][j][k].evaluate(pb);
                auto expected = (*out)[i].GetElementAtIndex(j).GetValues()[k];
                EXPECT_EQ(mod(pb.lc_val(out_lc[i][j][k]), q), FieldT(expected.ConvertToInt()));
            }
        }
    }
}

};  // namespace
