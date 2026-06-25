# BUG: memory_capabilities_spec failures — enum-field method call crash + match-on-dict.get SIGSEGV + RefEnv.consume copy loss

Status: FIXED (Bug A fixed 2026-06-11; Bugs B and C fixed 2026-06-22)

**Date:** 2026-06-11
**Status:** FIXED
**Severity:** High (two interpreter crashes + one silent wrong-result)
**Found by:** memory_audit_gc_nogc spec triage (.spipe/memory_audit_gc_nogc/t2_memory_capabilities_triage.md)
**Spec:** test/00_formal_verification/compiler/memory_capabilities_spec.spl (6/6 pass as of 2026-06-22)

## Bug A — method call on enum stored as struct field crashes interpreter

**Status: FIXED 2026-06-11**

`CapType.to_lean()` calls `self.cap.to_lean_name()` where `self.cap` is an enum value
stored in a struct field. Field retrieval succeeds; any subsequent method call on the
retrieved enum value crashed the `it` block.

**Root cause:** `interpreter_method/mod.rs` `Value::Enum` method dispatch only consulted
the local `enums` map and `impl_methods` — never `GLOBAL_ENUMS`. When the enum was
registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), both lookups missed,
the match arm fell through, and the interpreter emitted a "method not found" error
(surfacing as a block crash/abort).

**Fix:** Added `GLOBAL_ENUMS` as a third-tier fallback in the `Value::Enum` body-method
lookup path (`src/compiler_rust/compiler/src/interpreter_method/mod.rs`), mirroring the
three-tier probe already used in `interpreter_call/mod.rs` and
`interpreter/expr/calls.rs`.

**Regression spec:** `test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl`
(4 passing tests: standalone enum method, struct-field enum method, temp-var form,
round-trip of all three variants). `cargo check -p simple-compiler` clean.

## Bug B — `match dict.get(key)` SIGSEGV when value type is a class

**Status: FIXED 2026-06-22**

`match d.get(key)` where the dict value type is a class → interpreter exits 139.
Blocks the whole test body.

Fix: `RefEnv` no longer uses `match self.refs.get(name)` for class-valued
references. It uses its own `ref_names` / `ref_values` arrays for lookup and
mutation, with `refs` kept as a compatibility mirror.

## Bug C — RefEnv.consume mutates a Dict.get copy (silent wrong result)

**Status: FIXED 2026-06-22**

`RefEnv.consume()` (code under test in the spec) does `self.refs.get(name)`, mutates the
returned value, and never writes it back. Dict.get returns a value COPY, so
`is_available()` stays true after consume. Same root pattern as the documented
arrays/values-are-value-types + cross-module mutation loss limitations. Either the
language needs reference semantics here, or RefEnv must re-insert after mutation —
decide at language level, then fix RefEnv accordingly.

Fix: `RefEnv` now keeps parallel `ref_names` / `ref_values` arrays for its own
storage and mirrors writes to `refs` only for compatibility. `consume()` updates
the array slot after mutating the copied `Reference`, avoiding the crashing
`match self.refs.get(name)` class-value path and preserving the consumed state.

Evidence: isolated interpreter probes changed from `before=false` /
crash-prone dict behavior to all expected checks passing; the full
`memory_capabilities_spec.spl` now passes 6/6 in interpreter mode.
