# Simple native test binaries

Simple already provides compiled test execution through its own test runner.
When asked for test executables "like GoogleTest", use and repair that existing
feature. Do not introduce GoogleTest, another foreign framework, or a new test
registry merely because the requested workflow resembles one.

## Build and run with the existing feature

Use a source-matched self-hosted full CLI or standalone test runner and pin the
Phase 2 producer. The explicit AOT switches are `--native-backend=llvm` and
`--native-backend=cranelift`. `--mode=native` or `--mode=binary` alone is not proof
of machine-code execution: the ordinary Native path can build an SMF artifact.

Example PowerShell invocation (replace paths with the actual phase artifacts):

```powershell
$env:SIMPLE_BINARY = 'C:/path/to/phase2/simple.exe'
$env:SIMPLE_BIN = $env:SIMPLE_BINARY
$env:SIMPLE_NATIVE_BUILD_THREADS = '40'
$env:SIMPLE_NO_STUB_FALLBACK = '1'
$env:SIMPLE_NO_BOOTSTRAP_DELEGATE = '1'
$runner = 'C:/path/to/phase2/simple_test_runner.exe'
& $runner 'test/01_unit/compiler' --native-backend=llvm --unstable --assert-ran --no-cache --no-db --no-session-daemon --sequential --keep-artifacts --verbose --json
```

Run from the matching source root. If the producer requires an external runtime
bundle, set `SIMPLE_RUNTIME_PATH` to the actual receipt-bound runtime directory.
Use `--native-backend=cranelift` for the other backend and separate writable run
directories/caches. With the full CLI, insert `test` before the suite argument.
Forty is the compiler worker count; `--sequential` keeps spec processes from
each launching another uncontrolled forty-worker pool.

The maintained bootstrap wrapper is
[`run-native-aot-suite.shs`](../../../../scripts/bootstrap/run-native-aot-suite.shs).
It takes ten positional arguments: source root, backend, compiler path, compiler
SHA-256, runner path, suite path, private run directory, compiler threads,
runtime path (or `-`), and runtime identity. Its caller validates the phase
artifact receipts. It preserves the log and checks native AOT evidence.

The runner preprocesses each spec with Simple's existing result-bearing
wrapper, invokes `native-build`, runs the resulting executable directly and
collects its result. Explicit AOT errors remain errors; they are not replaced
with a successful interpreter run. `--keep-artifacts` retains generated test
artifacts, and `--verbose` records their paths and exact compiler invocation.

## Listing and counts

The runner's existing `--list` calls `list_tests_static`: this is source
discovery, not a query of the compiled executable's registered cases. Do not
report that result as a binary-owned test count. Likewise, source-file and
compiler-module counts are not executed case counts.

For a request to query each executable before running it, inspect that generated
binary's actual CLI and test entry. Use its supported list/count facility if
present; do not invent `--list-json`, `--gtest_list_tests`, or another flag.
The per-spec AOT path inspected here does not by itself prove a whole-subsystem
aggregate entry or a compiled listing command. Locate and repair the existing
entry/feature before proposing replacement infrastructure; unresolved listing
or aggregation is an explicit verification gap, not proof the feature is absent.

The Windows Phase 2 target matrix is six products: interpreter, loader and
compiler tests for each of LLVM and Cranelift. Keep discovered cases, built
executables, executed cases, PASS, FAIL, SKIP and BLOCKED separate for each row.
Compiler coverage includes core/HIR/MIR. A file-level build failure means its
cases were not executed; it is not a count of failed test assertions.

The provisional Phase 3/4 diagnostic schedule runs three native suite tasks
per backend after its independent Phase 4 binary builds have been attempted;
the full CLI and test runner must be available. This exposes independent build
failures before starting potentially long suites. The schedule verifies
their original manager manifests, receipts and hashes before and after each
task. `compiler-subsystem-test-inventory.shs` supplies all unit, integration and
system files owned by compiler, interpreter or loader, including sibling
compiler core/shared roots. Each file uses the existing native AOT wrapper with
40 compiler workers when the phase was configured for 40 threads. The two
backend lanes remain parallel; files within a lane run sequentially.

Results live under `phase4/native-tests/<backend>/<subsystem>/`. `results.tsv`
records each file's status, exit code and verified passing assertion count;
failed files retain `UNKNOWN` counts and their original logs. All independent
files continue after a failure. Empty or unavailable inventories are blocked.
Inventory hashes are checked before and after execution. `limitations.txt`
keeps aggregate executable and binary-owned listing support unverified: six
suite tasks are additional diagnostic coverage, not six aggregate binaries or
proof of 1000 executed cases. Provisional admission remains incomplete and
actual compiler/linker invocation provenance remains unproven.

## Repair and evidence

Continue independent files and suites after failures using the existing
`--unstable` route. Preserve nonzero results, failed logs and compatible caches;
fix shared compiler/runner/loader causes in parallel. A backend label or
`--mode=dynload` flag is not proof of a dynamically loaded backend provider.
Keep producer/runtime/provider evidence separate from test outcome evidence.

This guide records source-confirmed commands. It does not assert that the six
Windows Phase 2 test products have compiled or passed. Source trace and open
questions are in the [local research note](../../../01_research/local/simple_native_test_binary_workflow_2026-10-03.md).
