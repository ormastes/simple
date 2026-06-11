# BUG: memory_capabilities_spec failures — enum-field method call crash + match-on-dict.get SIGSEGV + RefEnv.consume copy loss

Status: OPEN

**Date:** 2026-06-11
**Status:** OPEN
**Severity:** High (two interpreter crashes + one silent wrong-result)
**Found by:** memory_audit_gc_nogc spec triage (.spipe/memory_audit_gc_nogc/t2_memory_capabilities_triage.md)
**Spec:** test/00_formal_verification/compiler/memory_capabilities_spec.spl (4/6 pass; the 2 failures are product bugs, intentionally left failing — no cover-up)

## Bug A — method call on enum stored as struct field crashes interpreter

`CapType.to_lean()` calls `self.cap.to_lean_name()` where `self.cap` is an enum value
stored in a struct field. Field retrieval succeeds; any subsequent method call on the
retrieved enum value crashes the `it` block. Standalone probes confirmed `\"` escapes in
interpolation are NOT the cause.

## Bug B — `match dict.get(key)` SIGSEGV when value type is a class

`match d.get(key)` where the dict value type is a class → interpreter exits 139.
Blocks the whole test body.

## Bug C — RefEnv.consume mutates a Dict.get copy (silent wrong result)

`RefEnv.consume()` (code under test in the spec) does `self.refs.get(name)`, mutates the
returned value, and never writes it back. Dict.get returns a value COPY, so
`is_available()` stays true after consume. Same root pattern as the documented
arrays/values-are-value-types + cross-module mutation loss limitations. Either the
language needs reference semantics here, or RefEnv must re-insert after mutation —
decide at language level, then fix RefEnv accordingly.
