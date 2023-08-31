#ifndef OPENFHE_PROOFSYSTEM_H
#define OPENFHE_PROOFSYSTEM_H

#include "ciphertext.h"
#include "cryptocontext.h"
#include "proofsystem_libsnark.h"

#include <typeinfo>
#include <utility>

#define PROOFSYSTEM_WIREID_METADATA_KEY "proofsystem_wireid"

using namespace lbcrypto;

class ProofsystemMetadata : public Metadata {
public:
    static std::string GetKey() {
        return std::string("proofsystem_metadata_") + typeid(ProofsystemMetadata).name();
    };
};

enum PROOFSYSTEM_MODE {
    PROOFSYSTEM_MODE_EVALUATION,
    PROOFSYSTEM_MODE_CONSTRAINT_GENERATION,
    PROOFSYSTEM_MODE_WITNESS_GENERATION,
};

using WireID = std::string;

class WireIdMetadata : public Metadata {
public:
    const WireID wire_id;

    WireIdMetadata(WireID wireId) : wire_id(std::move(wireId)) {}
};

template <typename Element, typename ConstraintMetadata, typename WitnessMetadata>
class ProofSystem : public CryptoContextImpl<Element> {
    static_assert(std::is_base_of<ProofsystemMetadata, ConstraintMetadata>::value,
                  "ConstraintMetadata is not derived from ProofsystemMetadata");
    static_assert(std::is_base_of<ProofsystemMetadata, WitnessMetadata>::value,
                  "WitnessMetadata is not derived from ProofsystemMetadata");

protected:
    std::unordered_map<WireID, WitnessMetadata> wire_id_to_metadata;

    virtual WireID GetWireId(ConstCiphertext<Element>& ciphertext) const {
        auto it = ciphertext->FindMetadataByKey(PROOFSYSTEM_WIREID_METADATA_KEY);
        if (ciphertext->MetadataFound(it)) {
            auto res = std::dynamic_pointer_cast<WireIdMetadata>(ciphertext->GetMetadata(it));
            return res->wire_id;
        }
        else {
            OPENFHE_THROW(openfhe_error, "Attempt to access metadata (WireIdMetadata) that has not been set.");
        }
    }

    virtual WireID GetWireId(Ciphertext<Element>& ciphertext) const {
        auto it = ciphertext->FindMetadataByKey(PROOFSYSTEM_WIREID_METADATA_KEY);
        if (ciphertext->MetadataFound(it)) {
            auto res = std::dynamic_pointer_cast<WireIdMetadata>(ciphertext->GetMetadata(it));
            return res->wire_id;
        }
        else {
            OPENFHE_THROW(openfhe_error, "Attempt to access metadata (WireIdMetadata) that has not been set.");
        }
    }

    virtual void SetWireId(Ciphertext<Element>& ciphertext, const WireID& wire_id) const {
        ciphertext->SetMetadataByKey(PROOFSYSTEM_WIREID_METADATA_KEY,
                                     std::make_shared<WireIdMetadata>(WireIdMetadata(wire_id)));
    }

    virtual size_t GetGlobalWireId()                  = 0;
    virtual void SetGlobalWireId(size_t globalWireId) = 0;

public:
    const CryptoContext<Element> cc;
    PROOFSYSTEM_MODE mode = PROOFSYSTEM_MODE_EVALUATION;

    template <typename E>
    using DoubleCiphertext = std::pair<Ciphertext<E>, Ciphertext<E>>;
    template <typename E>
    using DoublePublicKey = std::pair<Ciphertext<E>, Ciphertext<E>>;

    ProofSystem(const CryptoContext<Element> cc) : cc(cc) {}
    virtual ~ProofSystem() = default;

    virtual void SetMode(PROOFSYSTEM_MODE mode_) {
        this->mode = mode_;
    }

    virtual size_t GetNextWireId() = 0;

    virtual std::shared_ptr<CryptoContextImpl<Element>> GetCryptoContext() const {
        return cc;
    }

    template <typename T>  //, std::enable_if_t<std::is_base_of<ProofsystemMetadata, T>::value>>
    static void SetMetadata(Ciphertext<Element>& ciphertext, const std::shared_ptr<T>& metadata) {
        ciphertext->SetMetadataByKey(metadata.GetKey(), metadata);
    }

    template <typename T>  // , std::enable_if_t<std::is_base_of<ProofsystemMetadata, T>::value>>
    static void SetMetadata(Ciphertext<Element>& ciphertext, const T& metadata) {
        ciphertext->SetMetadataByKey(metadata.GetKey(), std::make_shared<T>(metadata));
    }

    //    static std::shared_ptr<ConstraintMetadata> GetMetadata<ConstraintMetadata>(ConstCiphertext<Element>& ciphertext) {
    //        auto it = ciphertext->FindMetadataByKey(ConstraintMetadata::key);
    //        if (ciphertext->MetadataFound(it)) {
    //            return std::dynamic_pointer_cast<ConstraintMetadata>(ciphertext->GetMetadata<ConstraintMetadata>(it));
    //        }
    //        else {
    //            throw std::logic_error("Attempt to access metadata (ConstraintMetadata) that has not been set.");
    //        }
    //    }

    template <typename T>  //, std::enable_if_t<std::is_base_of<ProofsystemMetadata, T>::value>>
    static T GetMetadata(const Ciphertext<Element>& ciphertext) {
        auto it = ciphertext->FindMetadataByKey(T::GetKey());
        if (ciphertext->MetadataFound(it)) {
            return *std::dynamic_pointer_cast<T>(ciphertext->GetMetadata(it));
        }
        else {
            throw std::logic_error("Attempt to access metadata that has not been set.");
        }
    }

    template <typename T>  //, std::enable_if_t<std::is_base_of<ProofsystemMetadata, T>::value>>
    static T GetMetadata(ConstCiphertext<Element>& ciphertext) {
        auto it = ciphertext->FindMetadataByKey(T::GetKey());
        if (ciphertext->MetadataFound(it)) {
            return *std::dynamic_pointer_cast<T>(ciphertext->GetMetadata(it));
        }
        else {
            throw std::logic_error("Attempt to access metadata  that has not been set.");
        }
    }

    virtual ConstraintMetadata PublicInputConstraint(ConstCiphertext<Element> ciphertext) = 0;
    virtual void PublicInputWitness(ConstCiphertext<Element> ciphertext)                  = 0;

    void PublicInput(Ciphertext<Element>& ciphertext) {
        SetWireId(ciphertext, "PublicCtxt(" + std::to_string(this->GetNextWireId()) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                // Nothing to do
                break;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                m = PublicInputConstraint(ciphertext);
                SetMetadata<ConstraintMetadata>(ciphertext, m);
                wire_id_to_metadata[GetWireId(ciphertext)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ciphertext, wire_id_to_metadata.at(GetWireId(ciphertext)));
                PublicInputWitness(ciphertext);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
    }

    virtual ConstraintMetadata EncryptConstraint(Plaintext plaintext, PublicKey<Element> publicKey) = 0;
    virtual void EncryptWitness(Plaintext plaintext, PublicKey<Element> publicKey,
                                ConstCiphertext<Element> ciphertext)                                = 0;

    Ciphertext<Element> Encrypt(Plaintext plaintext, const PublicKey<Element> publicKey) {
        Ciphertext<Element> ciphertext = cc->Encrypt(plaintext, publicKey);
        SetWireId(ciphertext, "Enc(" + std::to_string(this->GetNextWireId()) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ciphertext;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = EncryptConstraint(plaintext, publicKey);
                SetMetadata(ciphertext, m);
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                EncryptWitness(plaintext, publicKey, ciphertext);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ciphertext;
    }

    virtual void EncryptConstraint(Plaintext plaintext, DoublePublicKey<Element> publicKey,
                                   DoubleCiphertext<Element> ciphertext) = 0;
    virtual void EncryptWitness(Plaintext plaintext, DoublePublicKey<Element> publicKey,
                                DoubleCiphertext<Element> ciphertext)    = 0;

    DoubleCiphertext<Element> Encrypt(Plaintext plaintext, const DoublePublicKey<Element> publicKey) const {
        const DoubleCiphertext<Element> ciphertext(cc->Encrypt(plaintext, publicKey.first),
                                                   cc->Encrypt(plaintext, publicKey.second));
        SetWireId(ciphertext.first, "Enc_1(" + std::to_string(this->GetNextWireId()) + ")");
        SetWireId(ciphertext.second, "Enc_2(" + std::to_string(this->GetNextWireId()) + ")");
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ciphertext;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                EncryptConstraint(plaintext, publicKey, ciphertext);
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                EncryptWitness(plaintext, publicKey, ciphertext);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ciphertext;
    }

    virtual void FinalizeOutputConstraints(Ciphertext<Element>& ctxt, const ConstraintMetadata& vars) = 0;

    virtual ConstraintMetadata EvalAddConstraint(const ConstraintMetadata& m1, const ConstraintMetadata& m2) = 0;
    virtual void EvalAddWitness(ConstCiphertext<Element> ciphertext1, ConstCiphertext<Element> ciphertext2,
                                ConstCiphertext<Element> ciphertext_out)                                     = 0;

    Ciphertext<Element> EvalAdd(ConstCiphertext<Element> ctxt1, ConstCiphertext<Element> ctxt2) {
        auto ctxt_out = GetCryptoContext()->EvalAdd(ctxt1, ctxt2);
        SetWireId(ctxt_out, "Add(" + GetWireId(ctxt1) + "," + GetWireId(ctxt2) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = EvalAddConstraint(GetMetadata<ConstraintMetadata>(ctxt1), GetMetadata<ConstraintMetadata>(ctxt2));
                SetMetadata<ConstraintMetadata>(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                EvalAddWitness(ctxt1, ctxt2, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata EvalSubConstraint(const ConstraintMetadata& m1, const ConstraintMetadata& m2) = 0;
    virtual void EvalSubWitness(ConstCiphertext<Element> ciphertext1, ConstCiphertext<Element> ciphertext2,
                                ConstCiphertext<Element> ciphertext_out)                                     = 0;
    Ciphertext<Element> EvalSub(ConstCiphertext<Element> ctxt1, ConstCiphertext<Element> ctxt2) {
        auto ctxt_out = GetCryptoContext()->EvalSub(ctxt1, ctxt2);
        SetWireId(ctxt_out, "Sub(" + GetWireId(ctxt1) + "," + GetWireId(ctxt2) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = EvalSubConstraint(GetMetadata<ConstraintMetadata>(ctxt1), GetMetadata<ConstraintMetadata>(ctxt2));
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                EvalSubWitness(ctxt1, ctxt2, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata EvalMultNoRelinConstraint(const ConstraintMetadata& m1,
                                                         const ConstraintMetadata& m2) = 0;
    virtual void EvalMultNoRelinWitness(ConstCiphertext<Element> ciphertext1, ConstCiphertext<Element> ciphertext2,
                                        ConstCiphertext<Element> ciphertext_out)       = 0;
    Ciphertext<Element> EvalMultNoRelin(ConstCiphertext<Element> ctxt1, ConstCiphertext<Element> ctxt2) {
        auto ctxt_out = GetCryptoContext()->EvalMultNoRelin(ctxt1, ctxt2);
        SetWireId(ctxt_out, "MultNoRelin(" + GetWireId(ctxt1) + "," + GetWireId(ctxt2) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = EvalMultNoRelinConstraint(GetMetadata<ConstraintMetadata>(ctxt1),
                                              GetMetadata<ConstraintMetadata>(ctxt2));
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                EvalMultNoRelinWitness(ctxt1, ctxt2, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata EvalSquareConstraint(const ConstraintMetadata& m)                                 = 0;
    virtual void EvalSquareWitness(ConstCiphertext<Element> ciphertext, ConstCiphertext<Element> ciphertext_out) = 0;

    Ciphertext<Element> EvalSquare(ConstCiphertext<Element> ctxt) {
        auto ctxt_out = GetCryptoContext()->EvalSquare(ctxt);
        SetWireId(ctxt_out, "Square(" + GetWireId(ctxt) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = EvalSquareConstraint(GetMetadata<ConstraintMetadata>(ctxt));
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                EvalSquareWitness(ctxt, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata RescaleConstraint(ConstCiphertext<Element> ctxt_in, const ConstraintMetadata& m) = 0;
    virtual void RescaleWitness(ConstCiphertext<Element> ciphertext, ConstCiphertext<Element> ciphertext_out)   = 0;

    Ciphertext<Element> Rescale(ConstCiphertext<Element> ctxt) {
        auto ctxt_out = GetCryptoContext()->Rescale(ctxt);
        SetWireId(ctxt_out, "Rescale(" + GetWireId(ctxt) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = RescaleConstraint(ctxt, GetMetadata<ConstraintMetadata>(ctxt));
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                RescaleWitness(ctxt, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata EvalRotateConstraint(ConstCiphertext<Element> ciphertext, int rot_idx,
                                                    ConstCiphertext<Element> ctxt_out) = 0;
    virtual void EvalRotateWitness(ConstCiphertext<Element> ciphertext, int rot_idx,
                                   ConstCiphertext<Element> ctxt_out)                  = 0;

    Ciphertext<Element> EvalRotate(ConstCiphertext<Element> ctxt, int rot_idx) {
        auto ctxt_out = GetCryptoContext()->EvalRotate(ctxt, rot_idx);
        SetWireId(ctxt_out, "Rotate(" + GetWireId(ctxt) + "," + std::to_string(rot_idx) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = EvalRotateConstraint(ctxt, rot_idx, ctxt_out);
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                EvalRotateWitness(ctxt, rot_idx, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata RelinearizeConstraint(ConstCiphertext<Element> ctxt_in)                            = 0;
    virtual void RelinearizeWitness(ConstCiphertext<Element> ciphertext, ConstCiphertext<Element> ciphertext_out) = 0;

    Ciphertext<Element> Relinearize(ConstCiphertext<Element> ctxt) {
        auto ctxt_out = GetCryptoContext()->Relinearize(ctxt);
        SetWireId(ctxt_out, "Relinearize(" + GetWireId(ctxt) + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = RelinearizeConstraint(ctxt);
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                RelinearizeWitness(ctxt, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }

    virtual ConstraintMetadata KeySwitchConstraint(ConstCiphertext<Element> ctxt_in, const EvalKey<Element>& ek,
                                                   ConstCiphertext<Element> ctxt_out) = 0;
    virtual void KeySwitchWitness(ConstCiphertext<Element> ctxt_in, const EvalKey<Element>& ek,
                                  ConstCiphertext<Element>& ctxt_out)                 = 0;

    Ciphertext<Element> KeySwitch(ConstCiphertext<Element> ctxt, const EvalKey<Element> ek) {
        auto ctxt_out = GetCryptoContext()->Relinearize(ctxt);
        SetWireId(ctxt_out, "KeySwitch(" + GetWireId(ctxt) + "," + ek + ")");
        ConstraintMetadata m;
        switch (mode) {
            case PROOFSYSTEM_MODE_EVALUATION:
                return ctxt_out;
            case PROOFSYSTEM_MODE_CONSTRAINT_GENERATION:
                // TODO: we don't actually need to evaluate ctxt_out for constraint generation. Is this really a problem in practice?
                m = KeySwitchConstraint(ctxt, ek, ctxt_out);
                SetMetadata(ctxt_out, m);
                wire_id_to_metadata[GetWireId(ctxt_out)] = m.witness_metadata;
                break;
            case PROOFSYSTEM_MODE_WITNESS_GENERATION:
                SetMetadata(ctxt_out, wire_id_to_metadata.at(GetWireId(ctxt_out)));
                KeyswitchWitness(ctxt, ek, ctxt_out);
                break;
            default:
                throw std::logic_error("Unhandled mode: " + std::to_string(mode));
        }
        return ctxt_out;
    }
};

#endif  //OPENFHE_PROOFSYSTEM_H
