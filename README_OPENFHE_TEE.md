# OpenFHE in TEE

This branch is a fork of the [OpenFHE](https://github.com/openfheorg/openfhe-development) library, with specific examples to be benchmarked in `src/pke/examples/sok-*.cpp`. 
These examples can be built and run on CPU by following the [OpenFHE installation/building instructions](https://openfhe-development.readthedocs.io/en/latest/sphinx_rsts/intro/installation/installation.html). 

Our goal is to run and benchmark the same examples on a TEE (ideally intel SGX), by leveraging the [Gramine framework](https://gramine.readthedocs.io/en/stable/index.html). 
