# JIT SIGSEGV: field access on a `nil` receiver (`b.n` where `b` is nil)

**Date:** 2026-06-25
**Status:** RESOLVED 2026-06-25 — null guard added in Cranelift FieldGet/FieldSet codegen.
**Area:** Cranelift JIT codegen (`run`/`-c` path), NOT interpreter / type inference.
**Severity:** crash (SIGSEGV) — was a wild null deref; now a defined trap.

## Resolution

Root cause was misdiagnosed below. It is **not** a compile-time type-inference
recursion. It is a JIT codegen bug:

- `b.n` lowers to a plain `FieldGet` (`SIMPLE_TRACE_FIELD_GET=1` →
  `object=VReg(2) byte_offset=0 field_type=i32`), not a vtable dispatch.
- `compile_field_get` (`src/compiler_rust/.../codegen/instr/fields.rs`) masks the
  receiver's tag bits and loads from the pointer with **no null check**. A `nil`
  receiver masks to `0`, so the load faults at address `0x0` (`si_addr=0x0`,
  rip in valid JIT code) → wild SIGSEGV (rc=139).
- It surfaced now only because the JIT was re-enabled (native_profile / rt-symbol
  restore). On builds where the JIT still defers to the interpreter (production
  `bin/simple`, the older release seed — both fail JIT on `rt_len` NULL-jump),
  the interpreter reports the clean `undefined field 'n' on 'nil'` error (rc=1),
  which is why the older build "worked". The interpreter was never the crash site.

**Fix:** `builder.ins().trapz(obj_ptr, TrapCode::unwrap_user(12))` before the load
(FieldGet) and store (FieldSet). A nil receiver now hits a defined trap (rc=132,
the compiled-code analogue of a panic on nil access) instead of a wild memory
deref. Verified: repro no longer rc=139; non-nil and nested struct field
get/set still work (`Box(n:42).n` → 42, nested `l.a.x` → 3).

**Related logic bug — FIXED (interpreter) 2026-06-25:** typed optionals
(`i32?`, `text?`, ...) mishandled the Option API. Root cause: `cast_value` for
`Type::Optional` wrapped the value in `Value::Enum{Option, Some}`, violating the
interpreter's bare-payload convention (`None`=`Value::Nil`, present=bare
payload), so `unwrap_or`/`is_some`/`is_none`/`unwrap` never reached their
handlers. Fix (two sites):
1. `interpreter/expr/casting.rs` — Optional cast now keeps `nil` as `Value::Nil`
   and a present value as its bare payload (no `Some` wrap).
2. `interpreter_method/mod.rs` — the general primitive "method not found" path now
   falls through to `try_bare_some_option_method` (mirroring the Object path), so a
   present *primitive* optional (`mj: i32? = 7; mj.unwrap_or(9)`) gets the Option
   API. Verified: nil→`false/true/5`, present→`7/true/7`; plain `Some`/`None`,
   int/text/dict methods, and genuine unknown-method errors all unaffected.

**STILL OPEN — JIT/native backend:** the same typed optionals are unimplemented
in the JIT/native path (present optional renders as raw `<value:0xN>` via
`rt_value_to_string`, `unwrap_or` returns nil, `is_some` reported as "Function
not found"). Separate, larger codegen work — not addressed here. Also the
self-hosted `.spl` interpreter needs the parity fix (Rust/Simple parity) for
production `bin/simple` to benefit; this change only fixes the Rust seed.

---

> The analysis below is the ORIGINAL report; its "compile-time recursion" theory
> is incorrect (kept for history; corrected by the Resolution above).

## Repro (minimal)

```simple
struct Box:
  n: i32

fn main():
  val b: Box? = nil
  print "{b.n}"      # SIGSEGV (rc=139), no output at all
```

Run with `src/compiler_rust/target/bootstrap/simple run repro.spl`.

## Key observations (isolation)

- **Plain `nil` is fine.** `val x = nil; print "{x.n}"` → clean error
  `undefined field 'n': cannot access field on value of type 'nil'` (rc=1).
  Handled by the `_ =>` arm in `interpreter/expr/calls.rs:862`.
- **Only the type annotation differs.** The crash needs the receiver declared as
  an *optional struct* type (`Box?`). The runtime value is plain `nil`:
  `val b: Box? = nil; print "b is {b}"` prints `b is nil` and `b.?` is `false`
  (rc=0). So `b` evaluates to `Value::Nil`, yet `b.n` crashes only because of the
  `Box?` declared type.
- **The crash is at compile time, not runtime.** The failing run produces *zero*
  output (1-line log = only the shell's "Segmentation fault" line); the
  `[DEBUG FIELD ACCESS]` eprintln at `calls.rs:864` never fires. So the segfault
  happens during type inference / HIR lowering of the `b.n` access on an optional
  struct type — before the interpreter ever evaluates the field access.
- **No panic / no "stack overflow" message** → either deep type-inference
  recursion that faults the guard page silently, or a genuine bad deref.

## Regression window

- Works on the older Rust seed `src/compiler_rust/target/release/simple`
  (built 2026-06-23): the related program `nil.unwrap_or(Box(n:99))` then `.n`
  prints `ok 99` (rc=0).
- Crashes on a fresh `--profile bootstrap` build of the **current** seed source
  (2026-06-25). So a seed change landed between 2026-06-23 and 2026-06-25
  regressed optional-struct field-access type resolution into an infinite
  recursion / segfault. NOT introduced by this session's work (reproduced on a
  baseline build with no local seed edits).

## Related (same area, likely same root)

- `val mi: i32? = nil; mi.unwrap_or(5)` returns **`nil`** instead of `5`
  (typed-optional `nil` does not reach the `Value::Nil` Option arm at
  `interpreter_method/mod.rs:1064`; it is routed through a typed path that
  returns nil). Logic bug, no crash on its own — but feeding the wrong `nil`
  result into a field access is how the SIGSEGV above is reached in real code.

## Suspected root cause

The interpreter resolves `recv.field` using the receiver's *declared* type. For
an optional struct `T?` it appears to recurse through the optional/inner type
without a base case when the value is `None`/`nil`. Compare the inference
`enum Type` (`src/compiler/20.hir/inference/types.spl`): `Optional(inner: Type)`
is self-referential; a missing terminator on the `Optional` case during
field-type resolution would recurse forever.

## Suggested fix direction (unverified)

1. In the field-type resolution path, when the receiver type is `Optional(inner)`,
   resolve the field against `inner` exactly once (auto-unwrap), with an explicit
   recursion guard / depth bound so a cyclic optional type cannot loop.
2. Ensure a typed-optional `nil` value is `Value::Nil` end-to-end so it reaches
   the `Value::Nil => None` Option handling (fixes the `unwrap_or` returning-nil
   logic bug above too).
3. Add a runnable guard test (`b: T? = nil; b.field`) that must produce the same
   clean `undefined field … on 'nil'` error as plain `nil`, never a segfault.
