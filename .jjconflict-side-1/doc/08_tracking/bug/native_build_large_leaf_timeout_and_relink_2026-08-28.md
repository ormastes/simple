# Native-build large leaf timeout and warm relink cost (2026-08-28)

## Status

Open performance blocker with one recovered cache fix. The four leaves that
failed the Stage 4 full-CLI build's former 60-second per-file budget are real
cold-path outliers; `--timeout 0` distinguishes them but is not the fix.

Producer: `build/mini_builds/codex-stage3-head/simple`, Stage 3,
SHA-256 `7f26e3191656542f5a8aec680f5db8483000e35acd20b1f826dae88f9ef50791`.
Tree before the cache-wiring repair: `6010338e701f`. All probes used LLVM,
`core-c-bootstrap`, `dynload`, entry closure, `SIMPLE_NO_STUB_FALLBACK=1`,
`--timeout 0`, one build thread, and a private empty cache.

## Evidence

| Entry | Outcome | Compile/link | Max RSS |
|---|---:|---:|---:|
| `src/compiler/10.frontend/core/__init__.spl` cold | PASS, 231 compiled | 191.2s / 36.1s | 344,468 KiB |
| same cache, warm | PASS, 2 compiled + 229 cached | 21.2s / 50.1s | 187,724 KiB |
| `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` cold | PASS, 304 compiled | 585.3s / 44.2s | 1,156,528 KiB |
| `src/app/office/sheets/formula.spl` cold | terminated during convergence after exceeding 60s | codegen had emitted the module's unresolved-call inventory | at least 3,212,012 KiB observed |
| `src/app/cli/_CliMain/main_and_help.spl` cold | terminated during convergence after exceeding 60s | closure codegen was active | at least 1,615,696 KiB observed |

The core warm result proves object-cache reuse works, but native-build always
relinks the closure. Relinking alone exceeded the old 60-second budget under
concurrent bootstrap load. Phase tool caches must reuse a producer-bound final
binary and its receipt instead of invoking native-build again merely to obtain
the same output.

Formula is 8,716 lines / 386,701 bytes and reached more than 3 GiB while its
single module was in LLVM codegen. Method-call lowering is 4,501 lines /
271,753 bytes and spent nearly ten minutes in compilation. Both are candidates
for behavior-preserving module partitioning, but the MIR file is a semantic
owner under concurrent work and Formula has dense private cross-calls. Split
only with focused interpreter/native coverage; do not move functions blindly.

## Recovered cache regression

`src/app/cli/native_build_warm_receipt.spl`, its closure candidate publisher,
and its source-contract test survived the share-history merge, but
`native_build_main.spl` lost the consumer/promoter wiring. The repair restores:

- exact receipt preparation and candidate isolation;
- parse/HIR warmer suppression on an exact hit;
- candidate publication only to the authoritative real worker;
- promotion only after successful output-bearing zero-miss evidence; and
- environment restoration on exit.

The newer one-parse-shard memory clamp is preserved. This repair avoids
redundant warm-up children; it intentionally does not skip the authoritative
worker or linker.

## Remaining acceptance work

1. Add producer/hash/args/source-closure-bound final-artifact receipts for the
   full CLI and test runner in both Phase 2 and Phase 4 tool-cache lanes.
2. On an exact receipt hit, verify the immutable binary digest and copy/reuse it
   without frontend, MIR, LLVM, or link work.
3. Reprofile Formula and method-call lowering after the final-artifact cache is
   active. If cold construction remains a required sub-60-second gate, split
   the modules with semantic-owner review and focused regression tests.
4. Retain cold/warm wall time and max-RSS receipts in the bootstrap handoff.

