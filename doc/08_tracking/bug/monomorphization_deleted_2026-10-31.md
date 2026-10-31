# Monomorphization deleted (2026-10-31)

status: OPEN

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
