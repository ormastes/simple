# Item7 Phase3 compiler build: worker timeout and memory limit

Status: OPEN. Diagnostic build failed; this is not Phase3 admission evidence.

## Reproduction and immutable inputs

The feature branch targets `release_phase3`. Attempt 1 built
`src/app/cli/bootstrap_main.spl` from feature commit
`33c674a55b518b20679a21acd481d5f410d0b29b` using the private pure-Simple
producer SHA-256
`80030da7da3f15174dc26285389375b19c8f090c29eedb6bded089defaa28071`.
No Rust seed or stub fallback was used.

Packet: `C:/dev/simple-item7-phase3-toolchain-20261011/`.
Request: `request.json`, SHA-256
`4d2e8cdaffcde05983212080fe11a936af5160e3caf9576b879a42fff3c46a8a`.
Clean capture commit: `5d98e5d61ac661a85555516bd4627c2ccb6756e5`.
The app/compiler/lib trees exactly match the feature commit. The runtime
tree `581cd72c145ac010d02e1bd9c0198c82319179ce` differs only by a packet-local,
header-only `runtime_raw_u32.c` compatibility TU required by the producer's
legacy source list. It defines no symbols; the current `runtime_native.c`
remains the sole raw-u32 implementation owner. This composition is diagnostic.

The request uses LLVM, target `x86_64-pc-windows-msvc`, core-C bootstrap runtime,
explicit entry closure, one worker, a 900-second timeout, a 5 GiB enforced
process-tree RSS cap, and a 16 MiB bounded log collector.

## Actual attempt 1 result

`run/result.json` records compiler exit **124**, no executable, and a clean
capture after execution. `run/compile.rss.env` records `status=timeout`,
`quiescent=1`, `rss_cap_enforced=1`, `rss_limit_kib=5242880`, no unexpected
session PIDs, and `peak_rss_kib=4963552` (4.73 GiB). Both observed compiler
processes were gone after the watchdog returned.

The parent spawned one source-run worker:
`run src/app/cli/native_build_worker.spl ... --hir-shard=0/1`.
Before termination that child accumulated 435 seconds of CPU and used about
3.1 GB RSS while the parent waited. The retained terminal log reports
`[hir-shard] completed_workers=1 failed_workers=0 failed_modules=0 unfinished=0`.
This establishes HIR warm-worker completion, not a successful compiler build.

The complete retained stream is 465 bytes, with zero dropped bytes and SHA-256
`7b2c84474c1614602a448019f35db4c6fe6b17acb6a7e01f0fe5f67fdd934da4`.
It does not identify the worker's internal stage during the long CPU interval.

## Cause boundary and bounded continuation

An initial hypothesis attributed the delay to cold SCV inventory over a sparse
checkout's full Git index. The observed HIR child proves the parent had already
passed admission; inventory alone is not an established cause of this timeout.
The general producer route can run compiler worker source through interpretation,
including substantial compiler-module startup. Separating that startup from
active parse/HIR work requires more stage evidence.

Attempt 2 retains the same source, producer, runtime and compatible cache, writes
separate `run2/` receipts, disables the now-completed HIR warm-up with supported
`SIMPLE_HIR_SHARDING=0`, and enables bounded worker/closure/compiler traces.
It retains the same time/memory limits. No internal bootstrap-routing marker is
injected.

## Actual attempt 2 result

`run2/result.json` records compiler exit **88**, `status=rss-cap-exceeded`,
no executable and a clean capture. The final-worker spawn trace was reached;
no HIR warm-up worker was repeated. The resource receipt records
`peak_rss_kib=5244796` against limit `5242880`, `rss_cap_enforced=1`,
`quiescent=1`, and no unexpected session PIDs. This is a resource-aborted
failure, not a timeout or successful compile.

The complete retained stream contains 1666 bytes, with zero dropped bytes and
SHA-256 `f72dcf9b8a6a9bf7c992d73661890b4c7475d0b07e990be4a9176e07c4b48852`.
Request: `request-attempt2.json`, SHA-256
`fd65942591803a8d7700521d69ab730ea6273c8baa1eef25ad58d72aaf1f7473`.
The cache remains retained at its original producer/source/runtime-keyed path.
The final worker's internal phase is still not established by these logs.

The two changed attempts consumed the bounded execution allowance without
producing a candidate. Do not repeat either unchanged or relabel termination
as PASS. The next repair must address worker startup/working-set behavior or
establish an admitted source-matched compiler through the canonical bootstrap
flow; these diagnostics do not authorize bypassing source/runtime admission.

Hello World native sanity and the standalone adaptive loop probe are UNRUN until
a candidate executable exists. Full item7 Simple acceptance tests, source-matched
runner admission, general compiler loop instrumentation and broader typed join
support remain open. The narrow C capture selfcheck PASS does not close them.

## Producer-entry correction and focused routing repair

The producer's original build request at
`build/function-type-void-return-20261010/native-successor/request.json` pins
entry `src/app/cli/bootstrap_main.spl`, source commit
`1aff09312af1a48fba98634b6d59fcafe59b9602`, and executable SHA-256 `80030...28071`.
Its version/help also identifies it as a bootstrap compiler. That source already
dispatches marked, allowlisted worker children to compiled functions. Therefore
the earlier interpretation hypothesis is **not established** by the child argv,
CPU or RSS data. Neither retained failure receipt records an execution mode.
The failures establish time/resource exhaustion, not its internal cause.

Separately, the full CLI had no equivalent interception and handed these fixed
worker paths to ordinary source-run handling. The repair adds its compiled
dispatch before global flag filtering, while preserving source admission,
selected backend installation, inherited worker marker, fixed allowlist and
unchanged policy handoff. A shared backend-neutral worker entry removes duplicated
handoff validation from bootstrap and the legacy source fallback. Explicit
interpreter entry behavior and subprocess isolation remain unchanged.

The routing repair must not be described as a verified solution to the old
bootstrap producer's RSS failure. Seven authored routing contract scenarios
cover negative requests and exact payload preservation; execution and a rebuilt
compiler are required before claiming the repair verified. The next bounded
bootstrap diagnostic can use the supported single positional native-build route
to avoid retaining a coordinator and compiler worker simultaneously, without
injecting an internal marker or relaxing the memory limit.

## Routing probe diagnostics after the source repair

Source commit `e6693cd4baaf989519e26e652108177040d0dfe8` contains the
compiled full-CLI dispatch repair and shared worker owner. The private packet
`C:/dev/simple-item7-worker-route-fix-20261011` retains three changed attempts:

1. `probe-compile`: MSYS entry path, exit 1 before source loading.
2. `probe-compile-path-fixed`: Windows absolute entry path, exit 1 with zero
   sources. The entry collector excludes paths containing `/test/`, including
   this explicitly requested tracked fixture.
3. `probe-compile-explicit-copy`: a byte-identical copy outside the test tree,
   SHA-256 `C5D5062DAAEFA7237795AFFE00C43E9706A00198FEB3B6FDF97488DB9710CED7`.
   Both modules reached native code generation, then LLVM linking failed:
   `Required runtime source not found: C:/dev/simple-item7-phase3-20261011/src/runtime/runtime_raw_u32.c`.

The final receipt records exit 1, peak RSS 173592 KiB, enforced 5242880 KiB
limit, quiescent process tree and no unexpected session PIDs. Its complete
11885-byte log has zero dropped bytes and SHA-256
`4adfbc76cab16aebbe30dd08d75faff5b43d7c6ac0dc6076b1b2b04cb3760414`.
It also reports `rejected invalid array handle before dereference; probable
compiler/FFI ABI mismatch`; that diagnostic remains unresolved. MIR lowering
for two modules took 22038 ms, a concrete small-input performance concern.

The request set `SIMPLE_RUNTIME_PATH` to the frozen runtime capture containing
the documented header-only compatibility TU. The actual linker instead selected
the worktree runtime. Source inspection suggests the environment override is
supported, but these execution results do not establish why it was lost.
Repair runtime selection/compiled transport and explicit-entry test filtering
before the next verification cycle; do not add a shim to the user's checkout
or use the Rust seed to report a test PASS.

The three-attempt session limit is reached. No probe executable or new compiler
was produced, no helper assertion ran, and the prepared positional bootstrap
build was not launched because its prerequisite probe failed. STATUS: FAIL.
The full-CLI routing fix remains unverified and is not Phase3 admission evidence.

## Runtime-source repair and renewed Phase3 diagnostics

Source: `901d84fc04a591c828ec3e4e1029c5e4f7bd5c81`. Producer: the same
`80030...28071` bootstrap compiler from source `1aff093...`.

The runtime-source cause is confirmed: `find_runtime_source_dir()` reads
`SIMPLE_PROJECT_ROOT/src/runtime`, whereas `SIMPLE_RUNTIME_PATH` selects
archives. The repaired launcher sets the project root to the frozen capture
AFTER MSVC setup, retaining target cwd and `SIMPLE_LIB` for source imports.
Logger/watchdog environment rewriting was not the cause. The first repaired
compile then exposed an omitted sparse SDK dependency. Materializing the
existing `tools/counterpart/sdk/c` directory from the SAME capture commit fixed
that missing input without changing the runtime source tree. Header blob:
`7c65a95fa19c854efedd48ac0bab902fb0656ce4`; SHA-256:
`E1013C9B5F3DBC4AFC8AF728FE0CCEF1A4745F9C346CAC97A8919949AA17FFDD`.
Target runtime tree remains `808d12b3`; the frozen runtime retains its documented
header-only raw-u32 compatibility TU. Plugin ABI headers match across both roots.

### Confirmed executed passes

- `probe-compile-runtime-sdk-complete`: exit 0, build elapsed 199343 ms,
  peak 354124 KiB. Direct run: exit 0, `PASS: native worker routing checks=16`.
  Executable SHA-256:
  `d0fe9319291f046050aac5c7b9c0933b1184b8caac1da4ef5cd75a9cf7772915`.
  Complete 11951-byte compile log SHA-256:
  `5821596950946c27053f78b6dc153b7eca0d00dcc2d4bd1dbe23648c5b82eeaf`.
- Exact producer Hello World sanity: first 180-second diagnostic timed out
  at linking, exit 124, peak 231232 KiB. The observed successful 199-second
  probe justified a 300-second diagnostic retry. Retry: exit 0, elapsed
  222365 ms, peak 244052 KiB. Direct executable printed `hello`, exit 0.
  Artifact SHA-256:
  `D4750424B94DBBF33DAA57F26394CE898016B221A9596FD9624F992E10227243`.

Successful compile/run receipts are quiescent, enforce 5242880 KiB and report
no unexpected session PIDs. These passes do not execute SSpec, verify full-CLI
interception, or constitute formal Stage2/Stage3 admission. The Windows C-object
cache is distinct from the Simple module cache; timing alone cannot establish
C-cache hit counts. Module summaries report zero reused modules. Preserve the
completed runtime cache and all failed attempt evidence; do not rerun these
successful checks unchanged or claim unmeasured speedups.

### Provisional Phase3 build: FAIL

After Hello World passed, the supported positional direct-driver route attempted
`src/app/cli/bootstrap_main.spl`: LLVM, one thread, no stub fallback,
900-second watchdog, 5242880 KiB cap, rebased source and frozen runtime/SDK.
Packet: `C:/dev/simple-item7-worker-route-fix-20261011/bootstrap-main-build`.

The build discovered 1195 files and stopped with `rss-cap-exceeded`, exit 88,
peak 5245800 KiB. Its final receipt is quiescent with no unexpected session PIDs.
No executable was produced. Last retained HIR marker: 951/1195,
`compiler.frontend.core.capture_write_check`, elapsed 861305 ms.

The logger received 42411967 bytes, retained 16777216 and dropped 25634751.
Full received-stream SHA-256:
`a59214541177d1b1a545a52c25473e2d086b67046c675b8c7ce53db7e881c5e7`.
Retained log SHA-256:
`1f7cf4a770c457817c5b0b980e70f38322b044998e20e2147f5b11aae8a318b7`.
The live observer reports `PermissionError`; its stale 94/1195 marker does NOT
establish a several-minute single-module stall. Retained output confirms later
progress. Truncated retention and observer failure limit diagnosis, not the
nonzero memory-cap verdict. They cannot be promoted to PASS evidence.

The retained log names the canonical fail-closed K1 stub and does not name the
selected composition owner. The positional closure omits explicit composition
roots. Formal Phase3 must use the transcribed composition-root route and an
admitted parent; a positional artifact would not establish correct K1 admission.

The old producer generates extensive primitive re-export diagnostics. Its
re-export walk already has depth/cycle bounds and negative-result memoization;
recursive nonconvergence is not established. Target source already contains a
lowercase-builtin field-dependency guard in `module_import_registration.spl`
that is absent from the producer. Capitalized `Dict` must preserve user-type
precedence; globally suppressing it would hide unresolved ownership. Refresh
Phase2 and use correct composition roots before the next qualification attempt.
Memory growth and diagnostic volume are concrete failures of this producer.

Overall Phase3 STATUS: FAIL. Native helper and Hello World PASS remain valid;
compiler artifact, source-matched full tools and Phase3 admission remain missing.
