
#include "proofsystem/proofsystem_libsnark.h"

//#include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

#include "benchmark/benchmark.h"

using namespace std;
using namespace libsnark;
using ppT = default_r1cs_ppzksnark_pp;
typedef libff::Fr<ppT> FieldT;

protoboard<FieldT> init(size_t num_variables, size_t num_input_variables, size_t num_constraints) {
    libff::default_ec_pp::init_public_params();
    libff::inhibit_profiling_info     = true;
    libff::inhibit_profiling_counters = true;

    #pragma omp parallel
    {
        #pragma omp single
        std::cout << "#OpenMP threads: " << omp_get_num_threads() << std::endl;
    }

    protoboard<FieldT> pb;

    pb_variable_array<FieldT> vars(num_variables, pb_variable<FieldT>());
    vars.allocate(pb, num_variables, "x");
    pb.set_input_sizes(num_input_variables);

    cout << "Building constraint system";
    #pragma omp parallel for
    for (size_t i = 0; i < num_constraints; i++) {
        // Make R1CS 0.1-sparse, to model FHE workloads better
        linear_combination<FieldT> lc;
        for (size_t j = 0; j < num_variables; j += 10) {
            lc = lc + FieldT(i * j + 1) * vars[j];
        }
        #pragma omp critical
	pb.add_r1cs_constraint(r1cs_constraint<FieldT>(lc, lc, lc));
        if (i % (num_constraints / 100) == 0) {
            cout << ".";
            cout.flush();
        }
    }
    cout << endl;
    cout << "#variables:   " << pb.num_variables() << endl;
    cout << "#inputs:      " << pb.num_inputs() << endl;
    cout << "#constraints: " << pb.num_constraints() << endl;
    return pb;
}

const size_t num_variables       = pow(10, 4);
const size_t num_input_variables = num_variables / 10;
const size_t num_constraints     = pow(10, 4);

protoboard<FieldT>* global_pb;
r1cs_gg_ppzksnark_keypair<ppT>* global_keypair;
r1cs_gg_ppzksnark_proof<ppT>* global_proof;

static void BM_G16_BUILD(benchmark::State& state) {
    libsnark::protoboard<FieldT> pb;
    for (auto _ : state) {
        benchmark::DoNotOptimize(pb = init(num_variables, num_input_variables, num_constraints));
    }
    if (!global_pb) {
        global_pb = new protoboard<FieldT>(std::move(pb));
    }
}
BENCHMARK(BM_G16_BUILD)->Iterations(1);

static void BM_G16_SETUP(benchmark::State& state) {
    for (auto _ : state) {
        r1cs_gg_ppzksnark_keypair<ppT> kp = r1cs_gg_ppzksnark_generator<ppT>(global_pb->get_constraint_system());
        if (!global_keypair) {
            global_keypair = new r1cs_gg_ppzksnark_keypair<ppT>(std::move(kp));
        }
    }
}
BENCHMARK(BM_G16_SETUP);

static void BM_G16_PROVE(benchmark::State& state) {
    for (auto _ : state) {
        auto pi =
            r1cs_gg_ppzksnark_prover<ppT>(global_keypair->pk, global_pb->primary_input(), global_pb->auxiliary_input());
        if (!global_proof) {
            global_proof = new r1cs_gg_ppzksnark_proof<ppT>(std::move(pi));
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
