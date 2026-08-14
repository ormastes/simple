# Stage 3 self-host post-HIR segfault (2026-08-14)

## Reproducer

From a clean `origin/main` worktree, run:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=cranelift --deploy --no-mcp --jobs=2
```

## Evidence

- The deployed `release/x86_64-unknown-linux-gnu/simple test --help` crashes in
  `rt_env_set` while setting `SIMPLE_TEST_DEPTH`; its value argument is the
  invalid address `0x11`.
- Bootstrap cycle 1 rejected the multiline condition in
  `typed_storage_view_producer.spl` at the newline after `dest.?` and then
  crashed rather than returning the parser diagnostic cleanly.
- Cycle 2 crashed in
  `CompileContext.error_count()` from `CompilerDriver.lower_and_check_impl`.
- Replacing those internal accessor calls with direct reads of the scalar
  owned by `CompileContext.add_error` advanced cycle 3 through the first three
  HIR modules with `error_count=0` and into backend field processing.
- Cycle 3 still ended with exit 139 later in Stage 3. The bounded build log is
  `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

Higher-model review of the retained cycle-3 log narrows the last observable
frontier to pure-Simple MIR method-call lowering. The log ends while resolving
`push` with impossible receiver local ID `103079215111`; it contains no final
signal marker or backtrace, so this is a frontier, not a proved crash site.
Inspect receiver writeback/resolution at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2366-2403`,
`:2542-2695`, and the push specialization at `:2961+`. The source shape active
near the frontier is the pending/visited aggregate walk at
`src/compiler/35.semantics/value_struct_layout.spl:78-117`; adjacent semantic
coverage exists at
`test/01_unit/compiler/semantics/value_struct_layout_spec.spl:172-309`.

The direct scalar reads added in
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:353-357,449,489,505,526`
avoid the earlier invalid `CompileContext.error_count()` receiver. They do not
prove or repair the general receiver-corruption root cause. No passing result
from an exact native aggregate-receiver regression exists yet.

## Required follow-up

Capture the next post-HIR backtrace in a fresh lane, fix the pure-Simple owner,
add an exact native receiver regression plus one adjacent value-struct/push
case, then prove a provenance-verified Stage 4 full CLI with
`scripts/check/check-bootstrap-essential-tools-smoke.shs`. Stage 3 is a
prerequisite, not test admission. Do not substitute the Rust seed as test
authority and do not re-run the three exhausted cycles from this lane.

## Focused regression scaffold

The retained candidate-bound diagnostic scaffold initially used one combined
entry closure:

- `test/02_integration/compiler/stage3_aggregate_receiver_native_main.spl`
  executes the exact `CompileContext.error_count()` receiver before and after
  `add_error`.
- `test/02_integration/compiler/stage3_aggregate_receiver_spec.spl` mirrors the
  two source contracts for normal focused test execution after Stage 4 exists.
- `scripts/check/check-stage3-aggregate-receiver-native.shs` requires an
  explicit absolute pure-Simple candidate and an independently admitted digest
  in `SIMPLE_ADMITTED_COMPILER_SHA256`, plus the admitted runtime authority in
  `SIMPLE_ADMITTED_RUNTIME_PATH`. It rejects Rust-seed identities, hashes the
  candidate before and after, disables stub fallback, and retains build/run
  stdout, stderr, exit codes, candidate identity, and artifact hashes under a
  candidate-and-checker-hash-bound directory.

The third distinct focused cycle reached the exact native compiler invocation
and exited 139 before producing an executable. Its receipt is
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-13f1b7e0ed21a031/result.env`:
`build_rc=139`, `run_rc=125`, unchanged candidate hash, and no output artifact.
Stderr contains the timeout core-dump/segmentation-fault report but no
symbolized backtrace. This is a bounded exact reproducer, not a selected or
proved compiler fix. The three focused cycles are exhausted; AC-1 still
requires localization, a pure-Simple repair, and passing exact plus adjacent
native regressions in a fresh lane.

### Fresh-lane three-probe result

The exit-139 receipt does not prove that
`method_calls_literals.spl` owns the fault: both the exact receiver and its
large compiler entry closure were compiled in one invocation, and the receipt
has no internal trace. Therefore no speculative lowering change is admissible
yet. The next checker revision separates three entry closures and retains an
independent result for every one:

1. `stage3_compile_context_scalar_control_native_main.spl` imports and creates
   the same `CompileContext`, calls `add_error`, but replaces only
   `error_count()` with a direct `error_count_value` read.
2. `stage3_aggregate_receiver_native_main.spl` adds only the exact
   `error_count()` receiver behavior to that compiler closure.
3. `stage3_aggregate_push_control_native_main.spl` contains the adjacent
   array-of-aggregate push/projection shape without importing the compiler.

The checker records `error_count_receiver_candidate` only when scalar control
passes, the exact receiver fails, and adjacent push passes. If both
compiler-importing probes fail while adjacent push passes, it records
`compile_context_closure_or_add_error_candidate`. All eight PASS/FAIL tuples
have distinct labels, so an adjacent failure cannot overwrite evidence of a
second failure. Each probe also records whether failure occurred during build,
from build SIGSEGV specifically, from a missing executable, during execution,
or only in the output contract. These labels localize a boundary; none alone
closes AC-1. A source fix still requires uniquely proved ownership and all
bounded controls plus the three named regressions must pass afterward.

The single permitted run of this three-probe identity retained
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-054ce576790256e0-25383b77-1ed81de7-f44536be-93ec88d0`.
The candidate SHA-256 is
`0476f625056fc990d3fb45259285b7cbe433aaa8d3df2eae294001cf77589cf4`, the
runtime receipt SHA-256 is
`25383b7757608d90bb818599ac029826515ec90c2a97be082fa65a796bcda8d7`, and
the checker SHA-256 is
`054ce576790256e07bc71664bd38a021845a601cc158028bfc1f82b57f1d5bbe`.
Every probe had `build_rc=139`, `run_rc=125`, `build_sigsegv`, and no output
artifact; aggregate `result.env` records `FAIL-FAIL-FAIL`,
`localization=shared_or_multiple_failures`, and the same candidate hash before
and after. It remains non-localizing because the compiler-free adjacent push
also crashed during the build phase.

The exact run used the explicitly admitted Stage 2 and runtime authority:

```sh
SIMPLE_ADMITTED_COMPILER_SHA256=0476f625056fc990d3fb45259285b7cbe433aaa8d3df2eae294001cf77589cf4 \
SIMPLE_ADMITTED_RUNTIME_PATH="$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority" \
SIMPLE_ADMITTED_RUNTIME_RECEIPT="$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/runtime-admitted.txt" \
SIMPLE_ADMITTED_RUNTIME_RECEIPT_SHA256=25383b7757608d90bb818599ac029826515ec90c2a97be082fa65a796bcda8d7 \
sh scripts/check/check-stage3-aggregate-receiver-native.shs \
  "$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple"
```

Do not replay this checker/fixture identity. The artifact directory is
bound to the candidate, checker, runtime-admission receipt, and each fixture
hash prefix. Retain all full hashes, all per-probe build/run logs and results,
aggregate `result.env`, and the unchanged before/after candidate hash.

### Fresh-lane scalar baseline result

The next distinct identity added a compiler-free scalar-only baseline and one
struct-without-push control before the retained three probes. The scalar fixture
contains only scalar arithmetic, comparison, and `print`: no compiler import,
struct, array, or method receiver. The struct control adds only construction
and direct field projection: no compiler import, array, `push`, or method
receiver. It was run exactly once against the same admitted candidate/runtime
receipt and retained
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-5c722174dfee3cf8-25383b77-dd975615-26b60e80-1ed81de7-f44536be-93ec88d0`.

Its immutable inputs are candidate
`0476f625056fc990d3fb45259285b7cbe433aaa8d3df2eae294001cf77589cf4`, runtime
receipt `25383b7757608d90bb818599ac029826515ec90c2a97be082fa65a796bcda8d7`,
checker `5c722174dfee3cf885a8b402fcd6def5fd74c4184cb7d04c7790a2556bdeeacf`,
scalar baseline fixture
`dd975615117ec2be27e61c0864a18f7952bad8d31840ff9622c0f6e169eca8f2`, struct
control fixture `26b60e805edcdcf6e8ddae19fafef9a61c224d6d22d8c53c3a4afa63da02f8b6`,
and the retained scalar/exact/adjacent fixture hashes
`1ed81de77b7b137bd1538bc481b4839a5526a9b11fde2ad7500d7af377202377`,
`f44536bed9fe53d4496d718f8c8c035d9d37f0d15d5bf8a277298972588ec0c6`, and
`93ec88d090d9ef20e425af8ce34d3ac062b691b32594fc474b3e082cf290a778`.

All five probes produced `build_rc=139`, `run_rc=125`, `build_sigsegv`, and
no output executable. Aggregate `result.env` records
`probe_outcome=FAIL-FAIL-FAIL-FAIL-FAIL`,
`localization=general_native_build_candidate`, and unchanged candidate hashes.
The scalar-only build-phase failure determines that this receipt cannot support
an aggregate/shared-lowering attribution: the admitted candidate fails in the
general native-build path before any struct, array, or receiver shape is
required. It is not a source-owner fix selection and must not be replayed.

The separate record
`stage3_selfhost_exit_139_2026-08-14.md` describes an earlier infrastructure
lane with a different source authority, output directory, candidate hash, and
an empty child log. Its unretained exit-139 observation must not be presented as
the hash-bound cycle-3 frontier recorded here.

## Restart12 SimpleOS evidence

The nested-guard change in
`src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl` passed the
former multiline parse frontier. A strict LLVM
`--full-bootstrap --full-cli --no-mcp --jobs=min` run produced admitted Stage 2
SHA-256 `9c8757a5a31d5605b8765267789e0a2d1a882523ec84c523b740ed8ed3c55d10`
and then exited 139 later in Stage 3 MIR lowering. The retained log is
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`, SHA-256
`2dceab3fd116533537826b09b49cc64acfb2bfaaad6f9e5bd4036d5dd10af263`.
This lane exhausted its third attempt and stopped WARN.

## Restart12 render/CLI repair lane

Binary inspection proved the old `release/x86_64-unknown-linux-gnu/simple`
artifact is source-mismatched: it still lowers the test-depth update through
`.to_text()` and passes `0x11` to `rt_env_set`, while current full-CLI source
uses literal `"1"`. The lightweight `src/app/cli/test_entry.spl` still carried
the unsafe dynamic form and is corrected in this lane; its source-contract
tests now require the literal and reject `.to_text()`.

The Stage 3 frontier fix changes the aggregate-valued conditional that selects
`unresolved_receiver_local` into explicit typed `LocalId` assignments. This
preserves writeback/prelowered/fresh precedence and single evaluation while
avoiding the exact self-host aggregate-expression edge that emitted the
impossible receiver ID. A fresh isolated no-stub LLVM bootstrap is running at
`build/restart12-render-cli-fix`; only its retained result may promote this
from a hypothesis to a verified fix.

The first restart12 build cycle stopped earlier in Stage 2 on two concrete
optional-contract field reads: both `proof_uses` accesses were inferred from an
`ANY` owner. A cache-preserving second cycle returned the byte-identical log
immediately, proving stale native-cache reuse. The allowed fresh-cache third
cycle recompiled 476+ objects and reproduced the type error, proving it was not
only stale evidence. The next source revision routes each field read through a
helper whose argument is concretely `HirContractBlock`; this follow-up is not
build-verified in this exhausted cycle. Retained log:
`build/restart12-render-cli-fix/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`,
SHA-256 `cbdb55c0fce8d12780437ddab2d51529770e101c319db5af220dbd00fc097bf8`.

## Restart12 primary repair lane (2026-08-14)

The retained log proved that `MethodResolution.Unresolved` was selected by a
native `match`, while `rt_enum_discriminant(resolution)` returned the garbage
value `1851930204`.  That runtime helper expects the interpreter's tagged-Any
representation and must not inspect a self-host-native payload enum.  The
method-call lowerer now classifies `MethodResolution` through one exhaustive
language `match`; the source-contract regression is
`test/01_unit/compiler/driver/mir_method_enum_receiver_nil_guard_spec.spl`.
That focused spec passed 1/1 with the bootstrap seed as a diagnostic runner;
it is not self-host admission evidence.

The first rebuild also exposed an independently half-landed formal-verification
boundary: MIR consumers referenced `HirContractBlock` and
`HirFunction.verification_contract`, but canonical HIR defined neither in the
pre-rebase tree.  The concurrently landed `origin/main` now owns the complete
shared HIR types and propagation.  A strict cached rebuild subsequently
completed Stage 2 and entered Stage 3; the rebase retained upstream's canonical
definitions and dropped this lane's duplicate version.

The original impossible receiver/static-owner failure did not recur.  However,
the combined run was externally terminated with exit 143 during the quiet
Stage 3 build, and a cache-preserving
`--resume-stage3-from-admitted=build/bootstrap --jobs=1` was likewise terminated
with exit 143 after about ten minutes.  Neither retained log contains a compiler
error, signal backtrace, or completed Stage 3 artifact, so the correct status is
still **OPEN / BLOCKED**, not a compiler-crash claim and not PASS.

Resume condition: provide a supervisor window long enough for one materially
unchanged cache-preserving Stage 3 completion, then admit provenance and run a
real Stage4-from-admitted continuation (without rebuilding an already-green
Stage 3).  Retained evidence remains
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

## Terra evidence expansion (2026-08-14)

The retained candidate-bound three-probe diagnostic is now explicit evidence,
not a receiver-localization result.  With the admitted Stage 2 candidate
`0476f625056fc990d3fb45259285b7cbe433aaa8d3df2eae294001cf77589cf4`, run:

```sh
SIMPLE_ADMITTED_COMPILER_SHA256=0476f625056fc990d3fb45259285b7cbe433aaa8d3df2eae294001cf77589cf4 \
SIMPLE_ADMITTED_RUNTIME_PATH="$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority" \
SIMPLE_ADMITTED_RUNTIME_RECEIPT="$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/runtime-admitted.txt" \
SIMPLE_ADMITTED_RUNTIME_RECEIPT_SHA256=25383b7757608d90bb818599ac029826515ec90c2a97be082fa65a796bcda8d7 \
sh scripts/check/check-stage3-aggregate-receiver-native.shs \
  "$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple"
```

The three-fixture receipt at
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-054ce576790256e0-25383b77-1ed81de7-f44536be-93ec88d0/result.env`
records `FAIL-FAIL-FAIL`: scalar control, exact receiver, and adjacent push
each fail in the *build* with SIGSEGV; the candidate hash is unchanged. Its
`shared_or_multiple_failures` label therefore excludes a receiver-specific
root-cause claim.

A newer expanded receipt at
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-5c722174dfee3cf8-25383b77-dd975615-26b60e80-1ed81de7-f44536be-93ec88d0/result.env`
adds plain-scalar baseline and plain-struct controls. It records
`FAIL-FAIL-FAIL-FAIL-FAIL`, all `build_sigsegv` with build rc `139`, and the
same before/after candidate hash. The retained per-probe result files and
stderr logs are in that directory. This is a general native-build candidate
failure, not proof that any diagnostic fixture, MIR receiver path, or proposed
source edit is the root cause.

No newer retained Stage 3 success, Stage 4 executable, deployment lineage, or
essential-tools receipt was present during this inspection. Diagnostic focused
OS PASS observations do not change that admission boundary. The compiler
owner must take a fresh symbolized/backtrace-capable lane from this exact
provenance, preserve the probe artifacts, and hand the result to the
highest-capability reviewer before any Stage 4 claim.
