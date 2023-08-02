
#include "proofsystem/proofsystem_libsnark.h"

//#include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

#include "benchmark/benchmark.h"

using namespace std;
using namespace libsnark;
using ppT = default_r1cs_ppzksnark_pp;
typedef libff::Fr<ppT> FieldT;

protoboard<FieldT> init(size_t num_variables, size_t num_input_variables, size_t num_constraints) {
    protoboard<FieldT> pb;

    pb_variable_array<FieldT> vars(num_variables, pb_variable<FieldT>());
    vars.allocate(pb, num_variables, "x");
    pb.set_input_sizes(num_input_variables);

    for (size_t i = 0; i < num_constraints; i++) {
        // Make R1CS 0.1-sparse, to model FHE workloads better
        linear_combination<FieldT> lc;
        for (size_t j = 0; j < num_variables; j += 10) {
            lc = lc + FieldT(i * j + 1) * vars[j];
        }
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(lc, lc, lc));
    }
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
    return pb;
}

const size_t num_variables       = pow(10, 6);
const size_t num_input_variables = num_variables / 10;
const size_t num_constraints     = pow(10, 6);

protoboard<FieldT>* global_pb;
r1cs_gg_ppzksnark_keypair<ppT>* global_keypair;
r1cs_gg_ppzksnark_proof<ppT>* global_proof;

static void BM_G16_SETUP(benchmark::State& state) {
    libsnark::protoboard<FieldT> pb;
    if (!global_pb) {
        global_pb = new protoboard<FieldT>(init(num_variables, num_input_variables, num_constraints));
    }

    for (auto _ : state) {
        r1cs_gg_ppzksnark_keypair<ppT> kp = r1cs_gg_ppzksnark_generator<ppT>(global_pb->get_constraint_system());
        if (!global_keypair) {
            global_keypair = new r1cs_gg_ppzksnark_keypair<ppT>(kp);
        }
    }
}
BENCHMARK(BM_G16_SETUP);

static void BM_G16_PROVE(benchmark::State& state) {
    for (auto _ : state) {
        auto pi =
            r1cs_gg_ppzksnark_prover<ppT>(global_keypair->pk, global_pb->primary_input(), global_pb->auxiliary_input());
        if (!global_proof) {
            global_proof = new r1cs_gg_ppzksnark_proof<ppT>(pi);
        }
    }
}
BENCHMARK(BM_G16_PROVE);

static void BM_G16_VERIFY(benchmark::State& state) {
    bool verif;
    for (auto _ : state) {
        benchmark::DoNotOptimize(verif = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(
                                     global_keypair->vk, global_pb->primary_input(), *global_proof));
    }
}
BENCHMARK(BM_G16_VERIFY);

BENCHMARK_MAIN();