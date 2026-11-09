# LLVM backend silently no-ops Yield (silent wrong code, not an error)

## 2026-11-10 scoped LLVM backend regression PASS

Status: **fix implemented; scoped backend tests PASS; review/landing pending**.
The real LLVM-only Rust lib-test executable listed exactly the two new tests,
then executed both: **2 passed, 0 failed, 0 ignored** (4,826 unrelated tests
filtered out). The negative test exercised actual backend refusal on x86-64 and
x86. The positive test emitted real nonempty object bytes, ran production LLVM
optimization, verified the module, and checked the ordinary return value 42.

The executed test binary's SHA-256 was
`69afbc7e1c0e4952e59a1a015b8b40da31aaa2635f42f00aebc001776cac59a1`;
the reviewed and executed `functions.rs` bytes had SHA-256
`b8e16335874973dbffae92c2a4942dab0aa67e3f4521d874e86d02fae03f16ec`.
The normal enforced 8,000,000 KiB / 1,800-second Job Object guard exited 0,
reported quiescence, and measured peak job commit 4,764,872 KiB. Test execution
itself took 0.01 seconds. This qualifies these Rust LLVM backend regressions,
not self-hosted CLI admission, the optional legacy LLVM suite, or the full repo.

Actual execution used GNU LLVM 23.1.5 through the real MSYS2 LLVM import library
and matching LLVM-mingw CRT libraries first. A reviewed native linker wrapper
preserved actual arguments, response files and live temporary symbol inputs;
both dependency-DLL and compiler-test links completed with real Clang exit 0.
Private raw environment captures are retained locally and must not be published.
The wrapper's own controls are separate harness evidence, not LLVM test passes.

The four earlier failed attempts below remain failure history. One preservation
limitation is explicit: after the successful fifth link, Cargo/rustc automatically
removed all 257 intermediate object files. Their pre-run SHA-256/size inventory
and prior failure logs remain, but their bytes were not backed up before the
successful build. They must not be described as still retained or reconstructed
by rerunning green tests. The successful test executable, dependency cache and
complete actual-link response/symbol captures remain local.

## 2026-11-09 hard-error candidate preparation history

At this earlier preparation point, status was **fix implemented, verification
pending**. The LLVM MIR emitter now
returns a codegen error for `Yield` instead of dropping it. This protects direct
MIR compilation as well as callers that bypass the generator compilability
fallback. It does not claim generator support or change actor instructions.

Two LLVM-enabled Rust regressions exercise the actual backend: direct `Yield`
compilation must fail with the generator diagnostic on x86-64 and x86; an
ordinary constant-return MIR function must still compile and verify its IR.
Reverting the refusal would make the negative regression fail because the
backend would return success. These tests require the real LLVM feature and
provider; they are not source-text checks.

Execution was still pending at this preparation point. Source review or Rust formatting cannot
qualify the LLVM backend, and no self-hosted compiler/runtime smoke PASS is
claimed. The historical silent-drop evidence below is retained as the defect
baseline rather than presented as current verified behavior.

An actual private Cargo attempt with GNU LLVM 23.1.5 passed offline dependency
resolution and compiled dependencies, but stopped in `simple-runtime` because
the sparse source snapshot omitted
`src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h`.
No tests ran. Its retained watchdog receipt reports exit 101, quiescent cleanup,
and peak job commit 1,194,680 KiB under an 8,000,000 KiB ceiling. The attempt
also selected only `llvm`; the initial test placement required `llvm-tests` as well, so
even successful compilation would not establish regression execution. The
corrected invocation uses `--features llvm,llvm-tests` with the
`codegen::llvm_tests::function_compilation::test_mir_` filter and requires two
executed passing tests. The first retry was deferred to preserve the active
Phase-4 bootstrap priority. These preparation failures are not backend PASS
evidence.

After the Phase-4 attempt became quiescent, two corrected-feature attempts
retained that private dependency cache. The second attempt found one more
missing sparse input, `tools/counterpart/sdk/c/simple_counterpart_abi.h`, and
exited 101 with quiescent cleanup. After both runtime ABI headers were restored
from the pinned source, the third attempt reached the real compiler lib-test
build and failed with 29 errors. Existing compile-time test fixtures were
absent from the sparse source, and the optional LLVM test suite also used stale
APIs: private `mir::effects`, nonexistent `crate::mir::BinOp`, removed
`TypeId::Pointer` and `TargetArch::RiscV64` variants, obsolete MIR fields, and a
lifetime error in `llvm_test_utils.rs`. No broad legacy-suite repair was made.
The final receipt reports exit 101, quiescent cleanup and peak job commit
3,558,928 KiB. **Zero regression tests executed; verification remains blocked.**
All three attempt logs and receipts remain under the private worktree's
`build/review/llvm-yield-tests/`. A possible follow-up is to put the two direct
MIR regressions in an ordinary LLVM-enabled unit module and materialize the
full lib-test fixture closure.

The follow-up source candidate now places the two regressions in the existing
`functions.rs` unit module guarded by `all(test, feature = "llvm")`. The
optional legacy `llvm_tests/function_compilation.rs` file is restored exactly
to its pinned baseline; none of that stale suite is rewritten or reported as
passing. The new test names are
`codegen::llvm::functions::tests::llvm_yield_refusal_errors_on_x86_and_x64` and
`codegen::llvm::functions::tests::llvm_yield_refusal_preserves_ordinary_return`.
Both construct real MIR and call the actual LLVM backend.

Before any fourth compiler attempt, all 1,961 owned Rust source blobs at
`08cee705f035` were inspected through Git objects. Their 56 literal
`include_str!`/`include_bytes!` references resolve to 46 pinned fixture blobs,
all materialized; zero macro occurrences remained unclassified. The private
`literal-fixture-closure.sdn` records source references and fixture Git hashes.
This is input admission, not test execution. A reviewed follow-up must compile
with `--features llvm`, list and require those two tests in the resulting real
test binary, then execute both and require two passes.

The independently reviewed fourth attempt used that LLVM-only registration and
complete literal fixture closure. It compiled the real Rust lib-test code to
the final native linker, which then failed on `_MINGW_INSTALL_DEBUG_MATHERR`
referenced by LLVM-mingw's `crt2.o`. The explicit MSYS2 LLVM library search
preceded the driver's matching CRT archive search. The resulting mixed-CRT
selection is a real test-toolchain failure, not a successful regression run.
The receipt records quiescent cleanup and peak job commit 4,765,428 KiB.
No test executable, list, or body result was produced: **zero tests executed**.
At that point, all 257 generated objects were retained and hashed. Exact cached replay was not
possible because Rust removed its temporary `symbols.o`, and the diagnostic
omitted the full object argv. No replacement symbol object was fabricated.
A corrected CRT-search/capture-wrapper proposal was prepared privately for
independent review; at that point no fifth build or linker replay had launched.

- **Date:** 2026-07-19
- **Status:** open
- **Severity:** medium (no current in-tree consumer emits Yield through the
  LLVM path, but the failure mode is silent wrong code, not a diagnostic)
- **Area:** src/compiler_rust/compiler/src/codegen/llvm

## Symptom

A `gen fn` containing `yield` compiled through the LLVM backend produces a
function in which every `Yield` is dropped with no error, no warning, and no
runtime trap — the generator body runs as a plain function and yielded values
vanish.

## Evidence (source-confirmed, 2026-07-19 survey)

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1475` — `Yield`
  (with `ActorSend`/`ActorReply`) lowers to a literal empty block `{}`.
- Contrast: the Cranelift/JIT path has a real state-machine lowering
  (`codegen/instr/body.rs:542-1025`, `async_ops.rs:65-121`) via
  `rt_generator_*` externs, and native-build's compilability gate forces
  `FallbackReason::Generator` interpreter fallback (`compilability.rs:330,823`)
  — so the LLVM no-op is only reachable where that gate is bypassed, but when
  reached it is SILENT.
- Related open gaps: `doc/08_tracking/bug/async_await_interpreter_crashes_2026-06-11.md`
  (B3 history: JIT used to trap on yield; downgraded to nil-return),
  `std_async_runtime_native_backend_gaps_2026-06-11.md`.

## Expected

Either implement generator lowering on the LLVM path, or make `Yield` a HARD
compile error there ("generators unsupported on LLVM backend") so the failure
is loud. Silent-drop of a control-flow instruction is never acceptable.

## Context

Found during the wave-4 coroutine research
(`doc/01_research/hardware/nvme_fw_coroutine/embedded_coroutine_statemachine_research.md`),
which concluded `gen`/`yield` are unusable for baremetal firmware and adopted
explicit-state FSMs instead — this bug is why the research doc forbids citing
`gen`/`yield` as a working primitive anywhere AOT.
