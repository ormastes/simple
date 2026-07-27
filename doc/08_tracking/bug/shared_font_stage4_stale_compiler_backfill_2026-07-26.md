# Shared-font Stage 4 bootstrap admission blocker

- Date: 2026-07-26
- Status: BLOCKING — no admitted current-source pure-Simple CLI/core-C artifact
- Scope: shared-font runtime, docgen, native, surface, and release evidence

The earlier policy under `f1bcd0db5be` treated the compiler work as a separate
goal. That policy is superseded at `7e5595d98be`: shared-font completion now
requires a current-source pure-Simple Stage 4 CLI admitted with the core-C
runtime gate before focused runtime, docgen, native-device, performance,
hosted-WM, or QEMU evidence can count. A repeated full bootstrap is not
required when a bounded direct Stage 4 admission can prove the same gate.

The existing deployed Linux CLI is not admissible: SHA-256
`0d9856db5f29023ae9f06b19e68c686b791c0987842cb351d3df17363d0f7dc7`
self-identifies as Rust-built, and the essential-tools gate exits 1 with
`error=rust_seed_binary`.

An isolated current-source Cranelift bootstrap then exposed and removed a
worktree-only seed-directory symlink. With a regular local artifact tree, the
canonical provenance fingerprint passed as
`45691519492d518daa376fba19f160493a406e4d0b4df9dbe510da057f452ab8`.
No compiler, runtime, or product source was changed.

An earlier bounded campaign stopped before Stage 2:

```text
WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the existing Rust seed.
error: full CLI bootstrap refuses a stale compiler backfill; re-run with --full-bootstrap
```

This is a correct fail-closed owner boundary, not a reason to weaken admission
or use the Rust seed for tests. The retained seed/runtime/backfill tuple does
not match current source and must be rebuilt together.

Exact retained evidence:

- `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/summary.md`
- `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/cycle1/essential-tools-smoke.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/cycle2/bootstrap-console.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/cycle3/bootstrap-console.log`

Resume in a fresh bounded lane:

```sh
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```

For the current shared-font goal, only an exit-0 current-source result may
publish the immutable Stage 4 CLI path and SHA-256. The old artifacts below are
retained as history and cannot substitute for that blocking admission.

## Fresh full-bootstrap continuation

The documented full-bootstrap rebuilt and retained a current Rust
seed/runtime/compiler-backfill authority. Its first pure-Simple attempt then
failed before Stage 2 because the Stage 3 source snapshot opened a resolved
directory symlink as a file. The owner fix in
`scripts/check/lib/bootstrap-stage3/command-snapshot.shs` now records the
existing `link-dir-hex` entry before opening file targets. The provenance
self-test and a real checkout snapshot both pass; the latter records 23
directory links.

The second attempt admitted Stage 2 and Stage 3, then exposed missing
pure-Simple parser support for public module declarations. The shared
`parse_mod_decl` path now handles both `mod` and `pub mod`, with focused
coverage in
`test/01_unit/compiler/bootstrap/pub_mod_parser_spec.spl`. The retained hosted
probe prints `pub_mod_parser_probe=pass`.

At commit `033c0f9e6ae`, the current continuation produced and admitted for
stage progression:

- Stage 2:
  `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`,
  SHA-256
  `63523bc1f33c4705512279d126b1083b75296982699c5d51ca8d65b586b5b0ea`
- Stage 3:
  `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
  SHA-256
  `efe455723c76643c327312292769262f0a9326d91d424773e11d45611742103b`

Both Stage 2 and Stage 3 passed their recorded sanity gates. The retained
Stage 4 log proves the explicit-enum blocker cleared:

```text
phase2:parse:file:done src/os/kernel/types/syscall_types.spl
```

That attempt exited 1. Its first error was:

```text
src/std/skia/feature/shaper/ot_layout_gpos_data.spl:139:1:
unexpected token in expression: Indent
```

Its retained terminal log is:

`build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

No Stage 4 CLI/core-C admission artifact was produced in this historical lane.
That result remains useful diagnostic history, while the current admission
gate remains blocking.

Commit `dd1d266dc9e` then rewrote the GPOS block form. Cached Stage 4 cycle 2
cleared parsing, reached HIR, and exited 132 on a nil receiver. The retained
pre-fix trace in `build/native_probe/stage4-cycle3.log` first localized the
failure after the implementation-only
`src/compiler/backend/backend/compiler.spl` module.

That module has zero top-level functions and fifteen impl methods. The HIR
bootstrap branch inserted those methods into the returned `HirModule.functions`
but did not add them to the `_bootstrap_hir_functions` accumulator consumed by
the wrapper/module snapshot. Commit `e331a5700ab`, integrated as HEAD
`7a161abfabb`, now adds each typed `HirFunction` to both stores, retains typed
`HirModule` wrapper values, and adds
`test/01_unit/compiler/hir/bootstrap_impl_function_accumulation_spec.spl`.
The regression covers both 0 free + 2 impl and 1 free + 2 impl methods across
the returned HIR, accumulator, and per-module snapshot without drops or
duplicates.

The final cycle-3 check proved that boundary advanced:

```text
[hir-lower] lower_function:body process_function
[hir-lower] bootstrap-functions:count module=src/compiler/backend/backend/compiler.spl count=15
[HIR-BND] constructor:done
[HIR-BND] wrapper:return-received
[HIR-BND] store:add:done
[HIR-BND] driver:return-received
[HIR-BND] driver:errors-read:start
[HIR-BND] driver:errors-read:done
runtime error: field access on nil receiver
```

At the time, this trace suggested that the nil receiver was inside
`_driver_collect_hir_errors`, after the typed `[LoweringError]` array was read
and before collection completed. That historical inference motivated replacing
its `for err in errors` traversal with an indexed loop and an explicit
`LoweringError` binding. The direct
`test/01_unit/compiler/bootstrap/hir_lowering_error_collection_spec.spl`
regression covers empty, recovered, and fatal arrays through the shared driver
path. The source fix and regression are integrated but remain
execution-unverified. This trace is not the authoritative localization of the
later current-admission trap described below.

The historical three-check cap was reached. Its former completion policy under
`f1bcd0db5be` is superseded: the missing Stage 4 artifact blocks the current
focused runtime, docgen, native, and surface checks.

The current evidence scope is 32 generated manuals and 37 focused executable
runs. All require the admitted current-source pure-Simple CLI, retained output,
and `0 stubs`.

## Superseding current admission attempt

A fresh P0 owner ran exactly one bounded direct Stage 4 cycle from current
feature checkpoint `427878810b4b2d812dba129f6dfd1eb12e282989` plus isolated
compatibility bridge `d406b2688ed0096cc3d2758ba3753d2448261a99`. The bridge
was not merged into the feature branch. It preserved the 1,417-object cache
and used retained pure-Simple Stage 3:

`/home/ormastes/dev/pub/simple-bootstrap/build/bootstrap-memory-lexer-fix/stage3/x86_64-unknown-linux-gnu/simple`

Stage 3 SHA-256:

`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`

The exact invocation was:

```sh
env -u SIMPLE_COMPILER_PHASE_PROFILE -u SIMPLE_COMPILER_TRACE \
  -u SIMPLE_BOOTSTRAP_DIAG \
  RUST_LOG=error \
  SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_BOOTSTRAP_STAGE4=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=2 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR=/tmp/simple-cli-admission-20260727-5/build/bootstrap/native_cache \
  SIMPLE_RUNTIME_PATH=/home/ormastes/dev/pub/simple-bootstrap/src/compiler_rust/target/bootstrap \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_BINARY=/home/ormastes/dev/pub/simple-bootstrap/build/bootstrap-memory-lexer-fix/stage3/x86_64-unknown-linux-gnu/simple \
  /home/ormastes/dev/pub/simple-bootstrap/build/bootstrap-memory-lexer-fix/stage3/x86_64-unknown-linux-gnu/simple \
  native-build \
  --target x86_64-unknown-linux-gnu \
  --backend llvm \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib \
  --source examples/10_tooling \
  --entry-closure --low-memory --threads 2 \
  --cache-dir /tmp/simple-cli-admission-20260727-5/build/bootstrap/native_cache \
  --mode one-binary \
  --entry src/app/cli/main.spl \
  --runtime-path /home/ormastes/dev/pub/simple-bootstrap/src/compiler_rust/target/bootstrap \
  -o /tmp/simple-cli-admission-20260727-5/build/native_probe/simple-stage4-admission-once-427878810b4
```

The command exited 132 with terminal marker:

```text
runtime error: field access on nil receiver
```

The full command and output are retained at
`/tmp/simple-cli-admission-20260727-5/build/mini_builds/full_cli_admission_once_427878810b4.log`,
SHA-256
`e7dd548b18c976b9c75908029851222b90744cb3927e97de935ec83b65a10ca8`.
The requested Stage 4 ELF is absent, so the essential-tools smoke was correctly
not run. The one-cycle owner stopped at the first failure and performed no
retry; an identical retry is prohibited by the cap.

## Corrected current-admission localization

The earlier read-only inference that placed the repeated failure at
`HirLowering.lower_module`'s final diagnostic `eprint` is preserved only as
superseded history. The authoritative kernel record for the retained
current-admission process reports invalid opcode at instruction pointer
`0x559924`. In the exact retained Stage3 binary, that address is the `ud2`
immediately after `MethodResolver.resolve_expr` masks its incoming `expr`
argument and detects nil or a low-tag-only value. The call ABI itself is
normal (`rdi=self`, `rsi=expr`); the bad value arrives from the HIR traversal.

The retained trace proves that `src/lib/gc_async_mut/gpu/engine2d/color.spl`
completed all 28 HIR functions. Resolution then begins with `color_black`,
whose block tail is the Call `rgb(0, 0, 0)`. That trigger exposed a desugaring
contract split: `HirBlock` stores `has: bool` plus a mandatory `HirExpr`, but
five consumers still treated `block.value` as `Option` and five synthetic
constructors still supplied `Some(...)` or bare `nil`. In the failing path,
`resolve_block` interpreted the Call tail as an Option payload and could pass
the resulting nil or low-tag-only value into `resolve_expr`.

Current source integrates the ten-site repair:

- five consumers—method resolution, constant evaluation, constant folding,
  effect inference, and backend block visitation—gate the mandatory value with
  `block.has`;
- five synthetic-construction sites—host-GPU lane lowering, two MIR module
  fallbacks, integer-match default construction, and enum-match default
  construction—set `has` explicitly and provide either a typed tail or a
  `NilLit` sentinel;
- the typed indexed lowering-error collector remains integrated, with focused
  regression sources for its array handling and the Call-tail/empty-tail HIR
  invariant.

These are source fixes, not admission evidence. This documentation correction
ran no test or build, did not rebuild the retained Stage3 or produce Stage4,
and did not retry the failed command. The fixes are therefore
execution-unverified. No Stage4 ELF, Stage5, or essential-tools smoke exists;
`HIR-BOOTSTRAP-NIL-001` and the pure-Simple CLI gate remain blocking, and the
shared-font verification result remains `STATUS: FAIL`.

## Open TODO and bounded continuation

| TODO | Status | Required change and evidence |
|---|---|---|
| `HIR-BOOTSTRAP-NIL-001` | BLOCKING | Produce and hash a current-source pure-Simple Stage 4 CLI/core-C artifact, then pass essential-tools smoke against that exact binary before running the 37 focused executions and generating the 32 manuals. |

The command below is retained only as historical full-bootstrap context. It is
superseded by the bounded direct attempt above and must not be repeated in the
same verification window.

Historical full-bootstrap command:

```sh
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```

## Unverified downstream source changes

The same working tree contains three source-level follow-ups that do not alter
the blocker or constitute runtime evidence:

- prepared font batches now canonicalize the `hip` alias to `rocm`, with a
  direct configuration regression;
- degenerate Simple Web parsing now returns typed unavailable evidence and an
  intentionally unsupported GROUP so Engine2D cannot present blank pixels as a
  successful render;
- nested WM content frames now lower to ancestor-clipped IMAGE commands with
  resolved Engine2D image inputs instead of unsupported GROUP metadata;
- the shared nested-frame collector has behavioral source coverage for one
  valid reachable collection and fail-closed stale, duplicate, and orphan
  rejection.

All four remain unverified until an admitted current-source pure-Simple runtime
runs their focused specs.

## Final bounded repaired-compiler result

The direct bootstrap compiler paths now save, enable, and restore
`SIMPLE_NATIVE_ARENA_DECLS=1`, reusing the established focused-build pattern.
The focused regression keeps `left\0right` byte-exact in the native expression
arena. Independent static review found no P0/P1 issue.

The third and final bounded generation cycle also exported
`SIMPLE_NATIVE_ARENA_DECLS=1` to the retained pure-Simple Stage3 producer. This
cleared the prior Rust environment panic on `SIMPLE_BOOTSTRAP_EXPR_404_S` and
reached HIR lowering, then stopped with exit 132:

```text
runtime error: field access on nil receiver
```

No candidate ELF or essential-tools smoke exists. The exclusive cache remained
at 675 objects. The retained log is
`/tmp/simple-cli-admission-20260727-6.isfZoU/build/mini_builds/minimal_repaired_compiler_final_fb09.log`
with SHA-256
`5cd89facfb881ee5a5f5003941e9bdf486f87b90dc0fe36573ec6e7482b5e034`.
The three-cycle cap is reached; do not retry this command unchanged.
