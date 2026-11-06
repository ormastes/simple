# SMF execute API returns a resolved address without an explicit entry call

Status: OPEN — source-audit finding, runtime NOT_RUN / inconclusive.
Date: 2026-11-06. Owner: compiler SMF/JIT execution. No repair implemented.

## Evidence and scope

In the reconciled source, src/compiler/70.backend/codegen.spl:712 declares
CodegenPipeline.load_smf_and_execute with a contract to load and execute main.
It creates JitInstantiator, calls load_smf_metadata, requests
try_jit_instantiate("main"), and on Success returns Ok(address.unwrap()) at731.
The inspected function contains no explicit invocation of that address. This is
a mismatch between the visible wrapper behavior and its execution contract.
Instantiation internals were not exhaustively traced or executed in this audit;
therefore this is not proof that no side effect occurs inside a lower layer, nor
that every deployed runtime exhibits the suspected failure.

Observed caller chain:

1. src/compiler/80.driver/driver_api_interpret.spl:26 interpret_file tries
   try_load_smf_cached; a source/interface/ABI-fresh entry selects SmfExec at107.
2. src/compiler/80.driver/driver_orchestration.spl:420 dispatches execute_smf.
3. src/compiler/80.driver/driver_pipeline_execution.spl:41 calls
   k1_jit_lane_execute_smf_v1.
4. src/compiler/70.backend/backend/static_jit_lane.spl:61 invokes the installed
   lane's execute_smf_fn; absence of a linked lane is an explicit error.
5. src/compiler/70.backend/backend/static_backend_cranelift_jit_lane.spl:43
   calls load_smf_and_execute and wraps the returned integer as CompileResult.Success.
6. src/compiler/70.backend/codegen.spl:712–737 returns the resolved address in
   the success branch, rather than visibly obtaining main's return value.

A nonzero address or CompileResult.Success alone cannot establish that main ran.
Do not report this path as qualified execution or ownership parity on that basis.
Existing manifest freshness checks also do not constitute an ownership proof.

## Required reproduction and positive oracle

Using an admitted pure-Simple toolchain and a composition with a real supported
SMF execution lane, compile a valid fixture whose main prints the unique marker
SMF-MAIN-EXECUTED-ONCE and returns the chosen small integer37. Invoke both the
explicit SMF path and a verified cache-hit path in isolated subprocesses. Assert
that the marker appears exactly once and that the driver's returned value is37,
not merely that execution reported Success or produced a nonzero integer.
If CLI exit codes do not expose the return value, use the public typed result in
a compiled harness and assert the integer there; retain the subprocess marker
oracle for actual execution. A dependency initializer marker should likewise
appear exactly once before the main marker. Pair with a missing-main/invalid
artifact negative that emits no main marker and returns a real diagnostic.

The test must execute produced artifact bytes, not an arbitrary test address or
a substituted function pointer. Record runtime/compiler/artifact hashes and lane
configuration. A build without a linked SMF lane must be reported unsupported,
not treated as a passing positive. Until this reproduction runs, runtime status
remains NOT_RUN / inconclusive and the bug remains open.

## Repair constraints

First determine the exact instantiation contract and ownership of executable
mappings, argument passing and entry invocation. If instantiation only resolves
code, invoke main via the existing canonical ABI entry-call owner and return its
result; avoid inventing a second unchecked pointer-call boundary. Keep artifact
ownership admission before executable instantiation/invocation. The broader route
plan is doc/05_design/language/memory/remaining_execution_route_admission_2026-11-06.md.
