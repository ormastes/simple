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

The historical evidence scope was 32 generated manuals and 37 focused executable
runs. The 2026-07-29 audited current inventory is 46 focused commands and 42
font manuals plus four compiler-prerequisite manuals; these counts require the
admitted current-source pure-Simple CLI, retained output, and `0 stubs`.

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
| `HIR-BOOTSTRAP-NIL-001` | BLOCKING | Produce and hash a current-source pure-Simple Stage 4 CLI/core-C artifact, then pass essential-tools smoke against that exact binary before running the 46-command audited inventory and generating the 42 font manuals plus four compiler-prerequisite manuals. The former 37/32 counts are historical only. |

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

## Corrected final-cycle crash localization

The generic final-cycle localization above is superseded by the host kernel
record. At `2026-07-27 04:58:53 UTC`, process `simple[3533100]` trapped
`SIGILL` at RIP `0x88034b`:

```text
traps: simple[3533100] trap invalid opcode ip:88034b sp:7ffc14540750 error:0 in simple[404000+9b1000]
```

The producer was the retained Stage3 executable
`/home/ormastes/dev/pub/simple-bootstrap/build/bootstrap-memory-lexer-fix/stage3/x86_64-unknown-linux-gnu/simple`,
SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`.
In that exact ELF, `0x88034b` is the `ud2` at
`driver__driver___format_hir_lowering_error+0x7b`. The function has already
accepted a non-nil `LoweringError`, loads its `span` field, detects that span
as nil, prints the standard nil-receiver diagnostic, and traps before reading
`err.span.file`. This is not the earlier `MethodResolver.resolve_expr` guard.

The statically resolved call chain in the retained ELF is:

```text
cli.bootstrap_main.run_native_build_bootstrap
  -> compiler_driver_run_compile
  -> CompilerDriver.compile
  -> CompilerDriver.lower_and_check_impl
  -> _driver_collect_hir_errors
  -> _format_hir_lowering_error
  -> err.span.file
```

The retained Stage3 implementation of `_driver_collect_hir_errors` begins by
calling `rt_for_iterable(errors)`, indexes that materialized iterable, and
passes each resulting record to `_format_hir_lowering_error`. It therefore
does not contain the current source's typed indexed collector (`while
error_idx < errors.len()` plus `val err: LoweringError =
errors[error_idx]`). The kernel evidence localizes the malformed record at the
old collector/formatter boundary; it does not independently prove which
earlier operation made `span` nil.

No core was retained; `coredumpctl` is unavailable and the host core pattern
routes through apport. There is therefore no postmortem register or heap image
beyond the kernel RIP and static ELF mapping. The next producer used for this
lane must itself contain the current typed indexed lowering-error collector
fix. Re-running the retained Stage3 cannot activate source code that is absent
from that producer. The three-cycle cap remains binding: no unchanged retry or
further build is authorized.

## Successor3 Option admission handoff — 2026-07-29

This section supersedes the old-Stage3 collector as the current admission
frontier without changing its historical evidence.

### Immutable current result

- Current pushed handoff HEAD:
  `90cef240c91c4ec31ffd1aebbb95520d4cebec86`.
- Successor3 source checkpoint:
  `502b70b54602bc451ca11f10d8935723bbad5018`.
- Temporary Stage 2:
  `build/native_probe/memory-dispatch-fix/stage2-goal-successor3-simple`,
  SHA-256
  `dd7e747ad1e22bb71d46c5737d20d2d250146af70fdd3c621f66d7ab57ca26cf`.
- Producer log:
  `build/native_probe/memory-dispatch-fix/stage2-goal-successor3.log`,
  SHA-256
  `ad666b2454b9b071a2f356f1f37ad17e27735f1dfd4769736d8d9a62f6b75782`;
  it records `689 reused / 4 rebuilt`, zero failures, and a linked binary.
- Both retained gates under
  `build/test-artifacts/stage2-successor3-option-smoke3/` fail during
  compilation, before an output binary, with
  `runtime error: field access on nil receiver` followed by SIGILL:
  `option_class_representation` and `cross_module_option_payload`.
- The three-cycle gate is exhausted in this session. Stage 2 is diagnostic
  producer evidence only; no Stage 3, Stage 4, essential-tools, font, docgen,
  native, QEMU, or performance evidence is promoted.

The retained time receipt records a Stage 2 command using the bootstrap-only
Rust seed and runtime archive, but it does not hash-bind all producer inputs.
Their current hashes are
`443ddfeb0cacf815ad213b162213d724d0d67558bd5be151948b4ca6abdc3e64`
for `src/compiler_rust/target/bootstrap/simple` and
`12b684a063416c7440cc718aac598b7aaa8a1ffa518a2e712d4a0966f548a3cd`
for
`build/native_probe/memory-dispatch-fix/stage2-round-native-all/libsimple_native_all.a`.
A fresh window must revalidate them and create a complete runtime manifest.
These current hashes do not prove the exact historical inputs; neither is
acceptance evidence.

### Six-lane static localization

Static delta and source order make the first `.?` through the `ExistsCheck` arm
the leading candidate:
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2511-2535`.
Successor2 built both probes; successor3, whose relevant compiler change is
`502b70b5460`, fails while compiling programs whose first affected expression
is `.?`. The exact first executed violation remains unproven.

The repair must satisfy all three owner invariants:

1. `.?` remains an `i64` payload-or-canonical-nil value until the outer
   presence test. It must test `rt_is_some` before unwrapping, copy the raw
   present payload, emit nil `3` for absence, and attach HIR/layout metadata
   after the merge. It must not eagerly lower/decode the payload as the inner
   MIR type.
2. No fallback may decode `base_local`, the outer Option handle, as the
   payload. If a typed decode is needed after a presence check, it must consume
   the already-unwrapped local. This is the same correction already applied to
   `.unwrap()`/`.unwrap_or()`.
3. Optional-struct `if val` binding must not depend only on
   `local_mir_type_of(candidate) == I64`. `HirType?` lowers semantically to an
   Optional tuple, so a raw Option/nil handle must never reach
   `lower_type(type_)` or `aggregate_name_for_hir_type(type_)` as though it
   were a `HirType`.

The retained logs have no RIP or backtrace, so the first executed violation is
not yet proven. Do not guess between them. In one fresh diagnostic batch, use
three isolated generated probes with
`SIMPLE_MIRB_TRACE=1 SIMPLE_TRACE_FIELD_GET=1`:

- A: construct `Option<Box>`, assign `val owned = opt.?`, and return a
  constant; this adds only the ExistsCheck boundary;
- B: use `if val owned = opt.?: return CONSTANT`, with no payload field read;
  this adds optional-struct `if val` binding;
- C: use the same `if val` and return `owned.value`; this adds field/provenance.

If A fails, repair the ExistsCheck owner. If A passes and B fails, repair the
shared optional-struct `if val` binding. If A and B pass while C fails, repair
field/provenance resolution. In every case, keep
`test/01_unit/compiler/mir/option_variant_order_source_spec.spl` as the focused
source contract and cases 25/26 in `scripts/check/native-smoke-matrix.shs` as
the behavioral gates. Do not add another renderer/runtime shim or rewrite
valid font source.

### Fresh bounded producer order

1. Revalidate source, seed, runtime, command, cache lock, and output hashes.
2. Run the A/B/C diagnostic batch once against the immutable successor3. This is
   a new discriminating diagnostic, not an unchanged acceptance-smoke retry.
   Stop that batch after the first failing probe and route its owner; a
   diagnostic failure is not an acceptance PASS.
3. Apply one owner-level correction and build a newly hashed temporary Stage 2
   with the retained cache under its existing exclusive lock. Run case 25 once;
   stop on failure. Run case 26 once only after case 25 passes.
4. Produce current Stage 3 positionally from `src/app/cli/bootstrap_main.spl`
   with an exclusive cache and `SIMPLE_NO_STUB_FALLBACK=1`.
5. Produce Stage 4 incrementally from that hashed pure-Simple Stage 3 using
   `src/app/cli/main.spl`; a successful incremental artifact is authoritative
   and must not be replayed cleanly.
6. Hash-bind Stage 4/core-C, run essential-tools admission, deliberate-red,
   zero-example calibration, and the focused-result-wrapper preflight once
   before any font command or canonical docgen.

The fresh Option window has at most three total diagnostic/fix cycles:
A/B/C discrimination is cycle 1, the first fix plus case 25 is cycle 2, and
case 26 or one case-25 corrective rerun is cycle 3. Case 26 runs only if case
25 passes within that budget. Stage 3 and Stage 4 each get one initial run
after Option admission; either failure is recorded as a new blocker without an
unchanged retry in this window.

Stop on provenance drift, shared-cache writes, unchanged failure, signal,
timeout, absent ELF, unresolved stubs, or missing admission markers. Preserve
the cache and all logs. No full bootstrap and no Rust-seed acceptance
substitution.

The following is a reconstructed Stage 2 template. It fails closed until the
operator exports every required path. Record the full source/seed/runtime
manifest plus command, stdout, stderr, time, exit, cache owner, and output hash:

```sh
: "${ATTEMPT_ROOT:?export one immutable attempt root}"
: "${SEED:?export the hash-bound bootstrap-only seed}"
: "${PROVEN_RUNTIME_DIR:?export the manifested runtime directory}"
: "${STAGE2_CACHE:?export the exclusively locked cache}"
: "${STAGE2_CACHE_LOCK:?export the matching cache lock}"
: "${STAGE2_OUTPUT:?export the unique Stage 2 output}"
mkdir -p "$ATTEMPT_ROOT"
stage2_rc=0
/usr/bin/time -v -o "$ATTEMPT_ROOT/stage2.time" \
  timeout -k 30s 1200s flock -n "$STAGE2_CACHE_LOCK" \
  env RUST_LOG=error SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_INCREMENTAL=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_NATIVE_BUILD_RUST=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=2 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$STAGE2_CACHE" \
  SIMPLE_BINARY="$SEED" SIMPLE_RUNTIME_PATH="$PROVEN_RUNTIME_DIR" \
  "$SEED" native-build \
  --target x86_64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --threads 2 --cache-dir "$STAGE2_CACHE" --mode one-binary \
  --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$PROVEN_RUNTIME_DIR" -o "$STAGE2_OUTPUT" \
  >"$ATTEMPT_ROOT/stage2.log" 2>&1 || stage2_rc=$?
printf '%s\n' "$stage2_rc" >"$ATTEMPT_ROOT/stage2.exit"
[ "$stage2_rc" -eq 0 ] || exit "$stage2_rc"
```

Hash-bind the current source HEAD, seed, every runtime-manifest entry, cache
owner, command, exit, and output before promotion.

The Stage 3 template also fails closed until all inputs are exported:

```sh
: "${ATTEMPT_ROOT:?export the immutable attempt root}"
: "${NEW_STAGE2:?export the hash-bound new Stage 2}"
: "${PROVEN_RUNTIME_DIR:?export the manifested runtime directory}"
: "${STAGE3_CACHE:?export the exclusive Stage 3 cache}"
: "${STAGE3_CACHE_LOCK:?export the matching cache lock}"
: "${STAGE3_OUTPUT:?export the unique Stage 3 output}"
mkdir -p "$STAGE3_CACHE"
stage3_rc=0
/usr/bin/time -v -o "$ATTEMPT_ROOT/stage3.time" \
  timeout -k 30s 3600s flock -n "$STAGE3_CACHE_LOCK" \
  env -u SIMPLE_NATIVE_BUILD_RUST -u SIMPLE_BOOTSTRAP_STAGE4 \
  RUST_LOG=error SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=1 \
  SIMPLE_BINARY="$NEW_STAGE2" SIMPLE_RUNTIME_PATH="$PROVEN_RUNTIME_DIR" \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$STAGE3_CACHE" \
  "$NEW_STAGE2" native-build --target x86_64-unknown-linux-gnu \
  --backend cranelift --threads 1 --cache-dir "$STAGE3_CACHE" \
  --mode one-binary --low-memory --runtime-path "$PROVEN_RUNTIME_DIR" \
  -o "$STAGE3_OUTPUT" src/app/cli/bootstrap_main.spl \
  >"$ATTEMPT_ROOT/stage3.log" 2>&1 || stage3_rc=$?
printf '%s\n' "$stage3_rc" >"$ATTEMPT_ROOT/stage3.exit"
[ "$stage3_rc" -eq 0 ] || exit "$stage3_rc"
```

Hash-bind Stage 2, the complete runtime manifest, cache owner, command, exit,
and Stage 3 output before promotion.

The incremental Stage 4 template declares every inherited input and fails
closed:

```sh
: "${ATTEMPT_ROOT:?export the immutable attempt root}"
: "${STAGE3_OUTPUT:?export the hash-bound Stage 3}"
: "${PROVEN_RUNTIME_DIR:?export the manifested runtime directory}"
: "${STAGE4_CACHE:?export the exclusive Stage 4 cache}"
: "${STAGE4_CACHE_LOCK:?export the matching cache lock}"
: "${STAGE4_OUTPUT:?export the unique Stage 4 output}"
mkdir -p "$STAGE4_CACHE"
stage4_rc=0
/usr/bin/time -v -o "$ATTEMPT_ROOT/stage4.time" \
  timeout -k 30s 7200s flock -n "$STAGE4_CACHE_LOCK" \
  env -u SIMPLE_NATIVE_BUILD_RUST -u SIMPLE_COMPILER_PHASE_PROFILE \
  -u SIMPLE_COMPILER_TRACE -u SIMPLE_BOOTSTRAP_DIAG \
  RUST_LOG=error SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_NATIVE_INCREMENTAL=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=2 \
  SIMPLE_BINARY="$STAGE3_OUTPUT" SIMPLE_RUNTIME_PATH="$PROVEN_RUNTIME_DIR" \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$STAGE4_CACHE" \
  "$STAGE3_OUTPUT" native-build --target x86_64-unknown-linux-gnu \
  --backend llvm --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib \
  --source examples/10_tooling --entry-closure --low-memory --threads 2 \
  --cache-dir "$STAGE4_CACHE" --mode one-binary \
  --entry src/app/cli/main.spl --runtime-path "$PROVEN_RUNTIME_DIR" \
  -o "$STAGE4_OUTPUT" >"$ATTEMPT_ROOT/stage4.log" 2>&1 || stage4_rc=$?
printf '%s\n' "$stage4_rc" >"$ATTEMPT_ROOT/stage4.exit"
[ "$stage4_rc" -eq 0 ] || exit "$stage4_rc"
```

Before Stage 4 promotion, hash-bind its Stage 3 parent, complete runtime
manifest, cache owner, exact command, exit, output, and matching core-C
archive. Record whether `STAGE4_CACHE` was fresh or contained reusable objects;
do not claim reuse without a pre-run cache receipt. Retain that same exclusive
cache after the run. The old external parent and paths are forbidden.

Run essential-tools explicitly as
`SIMPLE_BINARY="$STAGE4_OUTPUT" sh scripts/check/check-bootstrap-essential-tools-smoke.shs`.
It must exit zero and contain each marker exactly once:
`essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
`essential_duplicate_checker_smoke=true`, and
`bootstrap_essential_tools_smoke=true`. Runner calibration then requires both
fixtures to exit 1 and contain `test-runner: spec failed` and
`test-runner: no examples executed`, followed once by
`test/01_unit/lib/test_runner_result_wrapper_spec.spl`.
