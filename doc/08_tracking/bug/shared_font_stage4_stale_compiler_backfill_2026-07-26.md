# Shared-font Stage 4 bootstrap admission blocker

- Date: 2026-07-26
- Status: BLOCKED at the three-check cap; fixes implemented, bootstrap unverified
- Scope: pure-Simple Stage 4 admission and essential-tools runner calibration

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

Only an exit-0 wrapper result may publish the immutable Stage 4 CLI path and
SHA-256. The wrapper's essential-tools smoke must then prove deliberate-red
and zero-example refusal before any focused font command runs.

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

No Stage 4 CLI/core-C admission artifact exists, so essential-tools,
deliberate-red/empty calibration, docgen, and font execution remain blocked.

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

The nil receiver is therefore inside `_driver_collect_hir_errors`, after the
typed `[LoweringError]` array is read and before collection completes. The
current working change replaces its `for err in errors` traversal with an
indexed loop and an explicit `LoweringError` binding. The direct
`test/01_unit/compiler/bootstrap/hir_lowering_error_collection_spec.spl`
regression covers empty, recovered, and fatal arrays through the shared driver
path. Both the fix and regression are implemented but bootstrap-unverified.

The three-check cap is reached. No further bootstrap retry is permitted this
session. No Stage 4 CLI/core-C admission artifact exists, so essential-tools,
deliberate-red/empty calibration, docgen, font execution, native promotion,
and surface evidence remain blocked.

## Open TODO and bounded continuation

| TODO | Status | Required change and evidence |
|---|---|---|
| `HIR-BOOTSTRAP-NIL-001` | FAIL — fixes implemented, bootstrap unverified, three-check cap reached | In a fresh session, verify the integrated impl accumulator and current typed-index error collector. Require `compiler.spl` to retain a nonzero function count, pass error collection without a nil receiver, and produce an exit-0 full CLI. Retain the prior cycle-3 and final Stage 4 logs as starting evidence. |

Only a fresh session may run the command below. Only exit 0 permits publishing
immutable CLI/core-C paths and SHA-256 values, then running essential-tools,
the two direct HIR regressions, and deliberate-red/empty-runner admission. All
downstream work remains blocked until admission.

Future fresh-session command after that prerequisite:

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
  resolved Engine2D image inputs instead of unsupported GROUP metadata.

All three remain unverified until the admitted CLI runs their focused specs.
