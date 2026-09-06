## Re-verified 2026-08-17 — STILL OPEN, symptom unchanged

`bin/simple run` on the exact repro from this doc still prints:
```
ready=nil ro=nil rsv=0
```
Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed banner). Fix
requires a seed/JIT change plus a rebuild — recorded as a blocker, not fixed
here (resource rules forbid building the main compiler in this lane).

# JIT: `@packed` bitfield field reads return `nil` (positional raw constructor)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-10 by stream M3, while restoring `NullBlockStatusRegister`'s
`@packed` bitfields (`null_block_status_register_lost_packed_bitfields_2026-08-10.md`).
**Binary:** `src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, 2026-08-09 23:10)

## Symptom

A `@packed` struct built with the *supported* single positional raw value
constructor reads its bitfields back as `nil` under JIT:

```simple
@packed
struct S:
    ready: u32:1
    readonly: u32:1
    reserved: u32:30

fn main() -> i64:
    var s = S(0)
    s.ready = 1
    s.readonly = 1
    print "ready={s.ready} ro={s.readonly} rsv={s.reserved}"
    0
```

prints `ready=nil ro=nil rsv=0` — no fallback, no diagnostic.

## Contrast

The named-field constructor form `S(ready: 0, readonly: 0, reserved: 0)` is
rejected by HIR lowering with

```
Unsupported feature: bitfield constructors currently accept exactly one positional raw value
```

which drops the whole module to the interpreter — and the interpreter gets it
right: `ready=1 ro=1 rsv=0`.

So the only constructor form the JIT accepts is the one it miscompiles, and the
only form that produces correct values does so by falling out of the JIT.

## Impact

`src/lib/nogc_sync_mut/driver/null_block_driver.spl` keeps the named-field
constructor deliberately, so `null_block_status_register()` is correct today
(verified: `ready=1 ro=1 rsv=0 rc=1`) at the cost of an interpreter fallback for
that module. Any consumer that switches to `S(0)` for JIT speed gets silent
`nil` reads.

## Root cause (confirmed 2026-08-10)

**Not a bitfield extraction bug — a `print`-argument type-inference bug.**
The bitfield shift/mask GET and SET lowering
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:197-246`
and `lowering_stmt.rs:353-430`) is correct. Proven directly:

```simple
var s = S(0)
s.ready = 1
var x = s.ready
print "x={x}"        # -> x=1   (CORRECT)
print s.ready         # -> nil   (WRONG, same expression, no intermediate var)
```

`var x = s.ready` round-trips correctly; passing `s.ready` straight to
`print` does not. So the field value is computed correctly — the bug is in
how `print` classifies the **static type** of a `FieldAccess` expression on a
`Bitfield`-typed receiver.

`print`'s builtin-call lowering
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs:510-544`)
has a special "flat-optional" branch: if the print argument's `arg.ty`
resolves (via `type_registry.get`) to `HirType::Pointer { inner, .. }` (the
representation used for `T?`), it treats the raw payload as a nilable value
and routes it through `rt_opt_i64_to_string`, which decodes low bit-patterns
as tags — the comment at line 502 documents this exact collision: "payload 1
-> nil". A bitfield field value of `1` (our `ready`/`readonly` bits) lands
exactly on that colliding sentinel.

This means the `FieldAccess` HIR node for `s.ready` is carrying `arg.ty` =
`HirType::Pointer{inner: u32}` (or similar), NOT the plain `u32` that
`get_field_info` for `HirType::Bitfield` actually returns
(`type_resolver.rs:739-744`, `Ok((idx, field_info.ty))` — a plain
`BitfieldField.ty`, never wrapped in `Pointer`). So somewhere between HIR
construction of the bitfield `FieldAccess` expr and this print-arg check, the
field's static type is getting (mis)represented as the flat-optional/nilable
`Pointer` wrapper — plausibly because bit-width-annotated fields (`u32:1`)
share type-inference machinery with nilable/optional field defaults and the
`:N` bit-width suffix is not distinguished from an optional marker at that
site. The `x = s.ready` path avoids the bug because assigning to a `var`
re-derives `x`'s type from normal var-decl inference (plain `u32`), which
does not hit the same misclassification.

This is a genuine, precisely localized defect, but it lives entirely in
`src/compiler_rust/**` (Rust seed HIR/MIR type inference for bitfield field
access interacting with the documented, previously-scoped-out flat-optional
tagged-value representation ambiguity referenced in the code comment at
`lowering_expr_builtin.rs:493-509`). Per this session's constraints,
`src/compiler_rust/**` must not be edited — so no fix is attempted here.

## Unblock

Fix belongs in the Rust seed: correct the static type recorded on a
`HirExprKind::FieldAccess` HIR node whose receiver type is
`HirType::Bitfield` so it is the plain scalar `BitfieldField.ty` (as already
correctly returned by `type_resolver.rs::get_field_info`'s `Bitfield` arm),
not a `Pointer`/optional wrapper — then `print`'s flat-optional branch in
`lowering_expr_builtin.rs:510-544` will no longer misfire on bitfield field
reads. Alternatively (or additionally): accept named-field bitfield
constructors in HIR lowering so the fast (positional) and correct (named)
paths are the same path — that does not fix this print-typing bug on its own
but removes the `S(0)`-only trigger surface.

**Status stays OPEN.** Not attempted here because the fix requires editing
`src/compiler_rust/**`, which this investigation session was constrained not
to touch.
