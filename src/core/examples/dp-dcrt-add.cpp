#include <iostream>
#include <vector>

#include "openfhecore.h"

using namespace lbcrypto;
using Element = DCRTPoly;

int main ()
{
    usint m         = 8;    // cyclotomic order - double the ring dimension
    usint towersize = 3;    // number of towers

    std::vector<NativeInteger> moduli(towersize); // CRT moduli
    moduli = {NativeInteger("8353"), NativeInteger("8369"), NativeInteger("8513")};
    std::vector<NativeInteger> rootsOfUnity(towersize); // primitive m-th roots of unity
    rootsOfUnity = {NativeInteger("8163"), NativeInteger("6677"), NativeInteger("156")};

    typename Element::Integer modulus(1); // calculate the overall modulus 
    for (usint i = 0; i < towersize; ++i) {
        modulus = modulus * typename Element::Integer(moduli[i].ConvertToInt());
    }

    // native poly params per tower
    auto ilparams0 = std::make_shared<ILNativeParams>(m, moduli[0], rootsOfUnity[0]);
    auto ilparams1 = std::make_shared<ILNativeParams>(m, moduli[1], rootsOfUnity[1]);
    auto ilparams2 = std::make_shared<ILNativeParams>(m, moduli[2], rootsOfUnity[2]);

    // populate data
    NativePoly ilv0(ilparams0);
    NativeVector bbv0(m / 2, moduli[0]);
    bbv0 = {"2", "4", "3", "2"};
    ilv0.SetValues(bbv0, Format::EVALUATION);

    NativePoly ilv1(ilv0);
    ilv1.SwitchModulus(moduli[1], rootsOfUnity[1], 0, 0);

    NativePoly ilv2(ilv0);
    ilv2.SwitchModulus(moduli[2], rootsOfUnity[2], 0, 0);

    auto ildcrtparams = std::make_shared<ILDCRTParams<typename Element::Integer>>(m, moduli, rootsOfUnity);

    std::vector<NativePoly> ilvector2nVector(towersize);
    ilvector2nVector[0] = ilv0;
    ilvector2nVector[1] = ilv1;
    ilvector2nVector[2] = ilv2;

    Element ilva(ilvector2nVector);

    NativePoly ilvect0(ilparams0);
    NativeVector bbv1(m / 2, moduli[0]);
    bbv1 = {"2", "1", "2", "0"};
    ilvect0.SetValues(bbv1, Format::EVALUATION);

    NativePoly ilvect1(ilvect0);
    ilvect1.SwitchModulus(moduli[1], rootsOfUnity[1], 0, 0);

    NativePoly ilvect2(ilvect0);
    ilvect2.SwitchModulus(moduli[2], rootsOfUnity[2], 0, 0);

    std::vector<NativePoly> ilvector2nVector1(towersize);
    ilvector2nVector1[0] = ilvect0;
    ilvector2nVector1[1] = ilvect1;
    ilvector2nVector1[2] = ilvect2;

    Element ilva1(ilvector2nVector1);

    // Plus method
    {
        Element ilvaCopy(ilva.Plus(ilva1));

        for (usint i = 0; i < ilvaCopy.GetNumOfElements(); ++i) {
            NativePoly ilv = ilvaCopy.GetElementAtIndex(i);
            NativeVector expected(4, ilv.GetModulus());
            expected = {"4", "5", "5", "2"};
            std::cout << "calc: " << ilv << std::endl;
            std::cout << "GT  : " << expected << std::endl;          
        }
    }

    return 0;
}