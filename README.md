zkOpenFHE - an OpenFHE fork with (zero-knowledge) proofs of computation
=====================================

Fully Homomorphic Encryption (FHE) is a powerful cryptographic primitive that enables performing computations over encrypted data without having access to the secret key.
However, FHE only achieves a relatively weak security notion (IND-CPA or IND-CPA-D), which is often insufficient for real-world deployments. 

The goal of zkOpenFHE is to be a drop-in replacement for the excellent [OpenFHE](https://github.com/openfheorg/openfhe-development) library, with the additional ability to prove the correct evaluation of an FHE circuit using a (zero-knowledge) succinct non-interactive argument of knowldege ((zk)SNARK). 

To achieve this, we mirror's OpenFHE's interfaces, and augment them under the hood with automatic constraint generation and extended witness computation, using [libsnark](https://github.com/scipr-lab/libsnark).

## Usage
<table>
<tr>
<th>OpenFHE</th>
<th>zkOpenFHE</th>
</tr>
<tr>
<td>

```cpp


c = cryptoContext->Encrypt(secretKey, x);


c_rot = cryptoContext->EvalRotate(c, 1);

c2 = cryptoContext->EvalMultNoRelin(c, c_rot);
```
</td>
<td>

```cpp
proofSystem = LibsnarkProofSystem(cryptoContext);

c = cryptoContext->Encrypt(secretKey, x);
proofSystem.PublicInput(c);

c_rot = proofSystem->EvalRotate(c, 1);

c2 = proofSystem->EvalMultNoRelin(c, c_rot);
```
</td>
</tr>
</table>

A `ProofSystem` has three modes:

* `PROOFSYSTEM_MODE_EVALUATION`: evaluate the FHE circuit, just like OpenFHE
* `PROOFSYSTEM_MODE_CONSTRAINT_GENERATION`:  generate the constraints corresponding to the FHE circuit and automatically optimize them
* `PROOFSYSTEM_MODE_WITNESS_GENERATION`: generate the extended witness for the FHE circuit, which is needed for proving correct computation

## Links and Resources
For a more complete overview of our project, have a look at [zkFHE.github.io](https://zkfhe.github.io), where you'll out more about what we're trying to achieve

## Installation

To install zkOpenFHE, refer to OpenFHE's General Installation Information: [readthedocs](https://openfhe-development.readthedocs.io/en/latest/sphinx_rsts/intro/installation/installation.html) for more information

Or refer to the following for your specific operating system:

- [Linux](https://openfhe-development.readthedocs.io/en/latest/sphinx_rsts/intro/installation/linux.html)

- [MacOS](https://openfhe-development.readthedocs.io/en/latest/sphinx_rsts/intro/installation/macos.html). Note that the libsnark backend will not build on Apple Silicon, but a fix should be available soon. 

- [Windows](https://openfhe-development.readthedocs.io/en/latest/sphinx_rsts/intro/installation/windows.html)


## Benchmarks and Examples

* [Benchmark for standalone libsnark on your system](benchmark/src/bench_libsnark.cpp)
* [Benchmark for an outsourced logistic regression](benchmark/src/bench_logistic_regression.cpp)

## Contributing
If you'd like to contribute, please [reach out](mailto:christian.knabenhans@epfl.ch)!
We're also very grateful if you [report issues](https://github.com/zkfhe/zkopenfhe/issues), big or small, or if you'd like to contribute some examples.