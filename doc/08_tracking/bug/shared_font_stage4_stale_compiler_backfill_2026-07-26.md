# Shared-font Stage 4 bootstrap admission blocker

- Date: 2026-07-26
- Status: BLOCKED after the sole current Stage 4 retry
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

The sole Stage 4 retry exited 1. Its first error is:

```text
src/std/skia/feature/shaper/ot_layout_gpos_data.spl:139:1:
unexpected token in expression: Indent
```

The retained terminal log is:

`build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

No Stage 4 CLI/core-C admission artifact exists, so essential-tools,
deliberate-red/empty calibration, docgen, and font execution remain blocked.

The shaping owner has a minimal block-form correction pending verification.
The next bootstrap retry remains gated until that verification passes. Then
rerun the exact command below with the same output path, preserving the
available authority and cache trees.

## Open TODO and bounded continuation

| TODO | Status | Required change and evidence |
|---|---|---|
| `GPOS-DATA-BLOCK-001` | FAIL — minimal block-form fix pending verification | Verify that the correction removes the line 139 unexpected `Indent` without weakening the GPOS data contract. Retain Stage 2/3 sanity and successful `SyscallId` parsing as prerequisites. |

After that focused verification passes once, lane A may run the next
cache-preserving Stage 4 retry with the command below. Only exit 0 permits
publishing immutable CLI/core-C paths and SHA-256 values, then running
essential-tools and deliberate-red/empty-runner admission. Focused font tests
come next. Docgen remains prohibited until the CLI is admitted and the
corresponding runtime spec passes.

Exact next-continuation command after that prerequisite:

```sh
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```
