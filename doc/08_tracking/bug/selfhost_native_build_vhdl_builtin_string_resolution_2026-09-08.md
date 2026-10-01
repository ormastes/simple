# Self-hosted native build loses cross-unit builtin method identity
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Open. This blocks production of an admitted pure-Simple compiler needed for the
Chromium oracle shared-library gate.

## Evidence

An independent macOS arm64 compiler build ran for 3654.28 seconds, reached LLVM
code generation, and exited without producing `build/macos-stage4-direct/simple`.
Maximum RSS was 3,913,531,392 bytes.

LLVM codegen reported unresolved builtin method calls throughout the source
closure, including `str_len`, `str_contains`, `str_starts_with`, `str_split`,
`str_repeat`, `bool_to_text`, and array helpers. VHDL was only one visible
consumer. The receiver was recognized as builtin, but the resolved symbol name
crossed HIR/MIR transport as a flattened frontend/library function instead of
the canonical runtime builtin.

## Root cause and correction

`HirSymbol.builtin_method_tag` preserved only `str.strip` and `str.lines`.
Resolved `str.len`, `str.contains`, and `str.starts_with` therefore lost their
builtin identity across the staged compiler boundary. The HIR scalar classifier
now assigns owner-qualified tags for those three methods, and MIR lowering maps
them to `rt_string_len`, `rt_string_contains`, and `rt_string_starts_with`.
The classifier remains character-code based so bootstrapping does not introduce
a staged text-equality dependency, and custom owners remain untagged.

The focused behavioral transport spec passes under the interpreter, including
positive checks for all five tags and negative checks for custom, flattened,
and unsupported names. A native entry-closure rebuild is still required before
the full defect is closed; other reported builtin families may need their own
typed transport tags if they remain after the text-method correction.

### 2026-09-08 cache-preserving Stage-2 result

A fresh canonical `bootstrap-from-scratch --full-bootstrap --stop-after-stage2`
run rebuilt the Rust seed, runtime authority, and compiler backfill before
starting the pure-Simple Stage-2 native build. The Stage-2 child remained
CPU-active and advanced its log, then exited normally with status 1 after
approximately 11 minutes in that phase. It produced no Stage-2 candidate or
admission receipts.

The exact-mangled cross-unit declaration correction moved the failure boundary:
the earlier VHDL `str_len`/`str_contains`/`str_starts_with` failures did not
reappear. Three fail-closed resolution errors remain:

- `CacheGatewayV1.virtual_source_store()` arrived as the bare
  `virtual_source_store` MethodCallStatic name after its trait receiver identity
  had been erased.
- Two `text.split_whitespace()` calls could not reach the real pure-Simple
  `common.text_advanced.split_whitespace` definition through either the use or
  import map.

These are not evidence for declaring synthetic `text.method` externs. The next
repair must preserve trait-method owner identity and make pure-Simple UFCS
definitions visible to native entry-closure resolution. The fail-closed LLVM
guard should remain in place. This result is the authoritative second full-build
cycle; do not repeat it unchanged.

### Final permitted full-build cycle

The third full-build cycle rebuilt the Rust authority and ran Stage 2 beyond the
previous failure time. It terminated with status 1 and produced neither a
candidate nor admission receipts. The explicit imports removed both prior
`split_whitespace` failures. Two errors remained:

- `virtual_source_store` still reached LLVM as a bare builtin-receiver static
  call. A focused Rust regression proves that preserving an authored trait
  parameter hint through MIR selects virtual slot zero, but the real imported
  `CacheGatewayV1` parameter does not retain that hint. The remaining loss is
  therefore earlier in cross-module HIR import/function-parameter construction.
- `compile_source_inventory.spl` advanced past `split_whitespace` and exposed
  `Array.remove_at` as another missing builtin method identity/implementation.

This is the mandatory three-cycle stop point. Do not launch another full
bootstrap in the same session. Continue only with narrow compiler tests for
cross-module trait parameter hints and `Array.remove_at`; a future fresh session
may consume their passing evidence before attempting a new full build.

Post-cycle narrow analysis established that the failed Stage-2 process executes
the pure-Simple compiler, whose current `TraitMethod` MIR arm is a statically
resolved direct call rather than a dynamic trait-object call. The registration
boundary has therefore been changed in the isolated bootstrap branch to static
polymorphism (`T: CacheGatewayV1`), allowing monomorphization to retain the
concrete gateway owner without weakening the interface contract. Separately,
the branch now carries the already-documented canonical `entries.remove(found)`
repair for the unsupported `Array.remove_at` call. Neither narrow correction has
been promoted to a new full-build claim in this session.

The available Rust bootstrap seed also rejects the repository-supported compact
`fn main:` spelling in the new native VHDL closure fixture (`expected LParen,
found Colon`). The fixture uses `fn main():` for bootstrap diagnostics, but this
seed-only parser result is not language-surface evidence and must not normalize
production Simple style.

The narrow closure fixture now executes successfully in the seed interpreter
and reaches all three VHDL operations, emitting
`PROBE VERDICT: PASS vhdl-builtin-text len=pass contains=pass starts-with=pass`.
This confirms the fixture itself is valid; it does not satisfy the native gate.
`test/02_integration/compiler/native_vhdl_builtin_string_resolution_spec.spl`
fails closed on a Rust seed, compiles with stub fallback disabled when an
admitted compiler is installed, rejects unresolved/unknown symbol diagnostics,
and executes the resulting candidate.

## Expected

Builtin text methods used by co-compiled plugins resolve consistently during
entry-closure native builds, and the build emits a runnable pure-Simple compiler.

## Acceptance

1. Pass the typed HIR/MIR builtin-tag behavioral spec once.
2. Reproduce with a narrow VHDL entry-closure fixture before another full build.
3. Prove generated MIR/native calls use canonical `rt_string_*` symbols.
4. Run one fresh full self-hosted compiler build and retain its provenance.

