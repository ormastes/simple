# Feature Expert: SFFI v2 Hardening

Use this note when work touches extern returns, dynamic calls, foreign pointers,
provider loading, generated bindings, or SFFI assurance.

## Canonical artifacts

- Requirements: `doc/02_requirements/feature/sffi_v2_hardening.md`
- NFRs: `doc/02_requirements/nfr/sffi_v2_hardening.md`
- Architecture/design: `doc/04_architecture/platform/sffi_v2_hardening.md`
  and `doc/05_design/platform/sffi_v2_hardening.md`
- Plan: `doc/03_plan/compiler/sffi/sffi_v2_hardening_plan_2026-08-21.md`
- Research: `doc/01_research/platform/sffi_v2_hardening_2026-08-21.md`

## Non-negotiable rules

1. Missing return, symbol, ABI, pointer, or unsupported conversion never becomes
   nil, zero, false, empty data, a dummy handle, or a passing/skipped test.
2. Raw calls are `unsafe(ffi)` and yield unvalidated foreign state until lift.
3. One compiler-owned typed contract drives every engine and generator.
4. Map absence/error precisely to `T`, `Option`, `Result`, or
   `Result<Option<...>>`; do not infer semantics from a zero value.
5. Ownership, allocator, destructor, bounds, encoding, unwind, and callback
   policy are executable contract fields.
6. Prefer a pure-Simple counterpart; extern ownership stays in the canonical
   no-GC sync owner.
7. P4 signing/provenance remains planned until implemented and verified.

Start with the existing RED return/weak-stub/byte-array fixtures. Preserve
positive controls and require cross-lane category parity.

