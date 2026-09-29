<!-- codex-architecture -->
# macOS Bootstrap and Reverse-Reference Harmonization — TLDR

**Status:** Proposed. The referenced merged plan is only on unintegrated commit
`7d4aac717e5`; current source has partial substrates, not the completed design.

## Decision

Build and admit native Phase2→3 chains independently on
`aarch64-apple-darwin` and `x86_64-apple-darwin`. Keep writable phase caches
isolated until atomic shared-CAS publication exists. Reuse only exact
producer-neutral semantic values or target-specific objects with compatibility
receipts. Compose a universal binary only from two independently admitted thin
Phase3 artifacts, then test it natively on both architectures.

## Current boundary

- Per-module witnesses/interface-gated native reuse: partial and implemented.
- AOP, block, and linker reverse maps: implemented only in narrow local forms.
- Complete persistent semantic reverse registry/red-green query database: absent.
- Cross-process/worktree/Phase2→3 CAS promotion: absent.
- Kernel/plugin-only bootstrap and universal pure-Simple admission: absent.

## Gates

Exact source/compiler/provider/SDK/target receipts; native Phase2 and Phase3
startup; causal no-op/body/interface edit invalidation; clean/incremental parity;
no shared writable cache before P4; wall/CPU/RSS/cache evidence; correct Mach-O
slice/import checks; full CLI/test runner and MCP/LSP smokes; no stubs or Rust
seed artifact substitution.

## Ownership

Sidecars: N/A until scheduled. Merge owner is the compiler bootstrap/cache
integration owner. Final review must be independent and normal/highest-capability.

See `macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`.
