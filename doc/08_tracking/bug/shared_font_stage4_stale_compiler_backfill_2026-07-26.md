# Shared-font Stage 4 blocked by stale compiler-backfill authority

- Date: 2026-07-26
- Status: BLOCKED after three bounded cycles
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

The final bounded attempt stopped before Stage 2:

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

The third and final continuation attempt produced and admitted:

- Stage 2:
  `ab2fad326fd6b01c641712fa7d740d722744735410e3180242a883641668529f`
- Stage 3:
  `e01d43ffb191f68fb8667fa7b882ce93de4244ad786773214c1ded9d49cae6c9`

Stage 4 then failed in a font-owner file, which this bootstrap lane must not
edit:

```text
[parser_error] line 200:1: unexpected token in expression: Indent ''
[parser_error_ctx] path src/std/skia/feature/shaper/ot_layout_shaper.spl kind 181 text ''
[parser_error] line 200:13: unexpected token in expression: : ':'
```

The source at lines 199–200 split an inline `if` result before an indented
`else`. The shaping owner rewrote that expression in canonical multiline
parser grammar; the existing shaper and selected Arabic/Devanagari specs cover
both positioning-complete branches. A fresh continuation may rerun the same
command above while preserving
`build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap`.
No Stage 4 CLI exists yet, so essential-tools, deliberate-red, and empty-runner
calibration remain blocked.
