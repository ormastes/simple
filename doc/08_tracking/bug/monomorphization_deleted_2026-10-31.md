# Monomorphization deleted (2026-10-31)

status: CLOSED (2026-11-01) — source residue removed; see "2026-11-01 closure" below

Repo owner direction: delete monomorphization, accept a temporarily broken
tree, then fix compile errors in follow-up PRs.

Deleted: src/compiler/40.mono and src/compiler_rust/compiler/src/monomorphize.
Resolved when the seed and stage2 build again without them.

## 2026-10-31 seed follow-up

Rust seed rewired without any specialization pass: generic functions lower
type-erased through HIR (single-letter type params resolve to `ANY`; other
unknown type names fail with `UnknownType` under strict lowering). Removed
`smf_writer.rs` template sections, `linker/lazy_instantiator.rs`, and the
integration tests that only exercised templates/specialization
(`generic_template_tests.rs`, `smf_template_integration_tests.rs`).
`bind Interface = Impl` no longer rewrites calls to static dispatch; the
HIR path ignores `InterfaceBinding` and keeps dynamic dispatch.
Remaining: stage2 (Simple sources under src/compiler) still references
`run_monomorphization`.

## 2026-11-01 closure (verified on origin/release/1.0.0 @ 7c7444b8682)

- `src/compiler/40.mono/` and `src/compiler_rust/compiler/src/monomorphize/` do not exist.
- `git grep run_monomorphization -- src` finds no Simple caller; the only hit is the
  name string in the Rust native stub table
  `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:44` (inert list entry).
- `git grep 'compiler\.mono\.\|MONO_SYMBOL_BASE' -- src` finds nothing; one doc comment in
  `src/verification/generic_impl_index/LazyBodyIndex.lean:5` still names
  `MonomorphizationPass` (historical model reference, not a dependency).
- Pure-Simple MIR still refuses direct generic-template calls (`refuse_generic_template_call`,
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:230`). That is the
  erased-body lane (packet E0 in `doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md`), not monomorphization residue.
- A full stage2 build was not run for this closure (docs-only packet E1).
