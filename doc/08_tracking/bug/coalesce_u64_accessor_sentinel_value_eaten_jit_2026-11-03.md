# `[u64].first() ?? d` returns `d` when the real element is 3 — JIT only

- **Filed:** 2026-11-03
- **Status:** OPEN. Silent wrong result on the Cranelift JIT.
- **Severity:** P3 (single value, easy to miss)
- **Class:** same as `coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17` (fixed for i8..i64/u8..u32).

`optionalize_array_accessor` (`src/compiler_rust/compiler/src/hir/lower/expr/helpers.rs`) excludes `u64`
elements because u64 boxing differs from the BoxInt family. `var us: [u64] = [3, 7]; (us.first() ?? 9)`
gives 9 on the JIT (interpreter: 3); identical on the deployed seed before the fix.
Fix: give u64 a tagged `T?` path (rt_value_u64 box/unbox) in the same helper.
Probe note: `test/01_unit/compiler/codegen/probe_coalesce_sentinel_collision_jit.spl` (comment, unasserted).
