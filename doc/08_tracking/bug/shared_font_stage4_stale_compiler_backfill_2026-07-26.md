# Shared-font Stage 4 blocked by stale compiler-backfill authority

- Date: 2026-07-26
- Status: BLOCKED after the final three-retry continuation
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

After the shaping owner corrected the canonical multiline GPOS expression, the
final retry 3 produced and admitted:

- Stage 2:
  `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`,
  SHA-256
  `1c1631f7b99a0d38205174a0ce50b68d2be194f38b28f8e6c11fc450bdc9dc96`
- Stage 3:
  `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
  SHA-256
  `2ab52126d893ddd3706d24818e83a9207bcec97e9f135ce6b2e401097e368be7`

The retained Stage 4 log proves the prior GPOS blocker cleared:

```text
phase2:parse:file:done src/std/skia/feature/shaper/ot_layout_gpos.spl heap_registry=7739886
```

Stage 4 then first failed on an explicit syscall enum value:

```text
src/os/kernel/types/syscall_types.spl:8:10: expected enum variant name, got =
[parser_error_ctx] kind 100 text '='
src/os/kernel/types/syscall_types.spl:8:12: expected enum variant name, got IntLit
[parser_error_ctx] kind 1 text '0'
```

The source is `Exit = 0`. The pure enum parser at
`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` consumes a
variant identifier, optionally parses only a payload, then records the name.
Unlike the Rust parser, it never accepts `TOK_ASSIGN` plus a discriminant.
Merely skipping `= N` is invalid because the flat `decl_enum_def` and typed
`Variant` carry no discriminant, which would silently lose numeric syscall ABI
values.

Retry 3 exited 1 at `stage4-native-build`. The 302125-byte terminal log is:

`build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

The hard retry cap is exhausted; there is no retry 4 in this continuation.
No Stage 4 CLI/core-C admission artifact exists, so essential-tools,
deliberate-red/empty calibration, docgen, and font execution remain blocked.

Before a fresh continuation, implement end-to-end explicit discriminant
preservation in the pure flat AST, bridge/typed `Variant`, and downstream enum
lowering, with a focused non-sequential `SyscallId` regression. The only
alternative is an architecturally reviewed exclusion of this OS module from
the CLI closure. Then rerun the exact command above with the same output path,
preserving Stage 2/3 and native-cache trees.

Exact next-continuation command after that prerequisite:

```sh
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```
