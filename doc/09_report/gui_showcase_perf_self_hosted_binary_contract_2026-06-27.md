# GUI Showcase Perf Self-Hosted Binary Contract

Date: 2026-06-27

## Scope

This report covers the 4K/8K retained GUI showcase performance evidence
contract. New evidence must use a repo-local self-hosted Simple binary or an
explicitly supplied non-seed Simple binary. The Rust seed
`src/compiler_rust/**/simple` is forbidden for 4K/8K perf rows.

## Changes

- `scripts/check/check-widget-showcase-4k-200fps.shs` now discovers
  self-hosted release binaries under `release/**/simple` and `bin/release/**`
  before opt-in PATH lookup.
- The wrapper no longer defaults to `src/compiler_rust/target/release/simple`.
- Explicit Rust-seed `SIMPLE_BIN` values fail closed with
  `rust-seed-simple-binary-forbidden`, including `PLAN_ONLY=1`.
- The aggregate GUI RenderDoc status checker rejects 4K/8K rows whose
  `*_simple_bin` points at `src/compiler_rust/**` or whose
  `*_simple_bin_source` is a missing/default seed-style source.

## Verification Boundary

This contract hardens provenance for future 4K/8K evidence. It does not by
itself rerun live 4K/8K performance or prove RenderDoc, Vulkan, Metal, D3D12,
browser backing, production parity, or full CSS completion.
