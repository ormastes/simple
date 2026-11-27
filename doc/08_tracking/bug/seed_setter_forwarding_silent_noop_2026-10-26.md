# Seed: `obj.name = v` silently ignored `set_name` (wrong result, exit 0)

- **Severity:** P0 (silent wrong result)
- **Status:** fixed (this change)
- **Component:** Rust seed interpreter, `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
- **Spec:** `test/01_unit/language/accessor_forwarding/accessor_forwarding_spec.spl`

## Symptom

```simple
class Temp:
    _c: i64
    fn get_celsius() -> i64: self._c
    fn set_celsius(v: i64): self._c = v

var t = Temp(_c: 10)
t.celsius = 40          # did nothing
print(t.get_celsius())  # printed 10, exit 0
```

The seed had getter forwarding (`get_`/`is_`/no-paren, `interpreter/expr/calls.rs`)
but no setter half. `t.celsius = 40` inserted a dynamic field `celsius` on the
instance; the setter never ran, and nothing was reported. Assignment to a name
that is neither a field nor has a setter was likewise accepted silently.

Red (old seed `bin/simple.exe`, interpreter): `class_set=10 want=40`,
`class_is_after=false want=true`, `struct_set=1 want=7`; undefined-field probe
printed `SILENT_NOOP value=10` with exit 0.

## Fix

`forward_field_setter` runs before the plain `obj.field = v` store: when the
receiver's class is known and `field` is not a declared/present field,
`obj.set_field(v)` is called (through `handle_method_call_with_self_update`, so
a struct `me set_x` writes back); with no setter it is a hard E1012
`undefined field 'x': class C has no such field or setter`. `_`-prefixed names
keep their backing-field auto semantics (mirrors the getter's `_` auto-zero),
and a real field always beats a setter (`field_beats_setter=5/0`).

Not covered (unchanged): augmented assignment `t.celsius += 1` on a forwarded
name, and `arr[i].name = v`.

## Self-hosted compiler parity

`src/compiler/**` has **no** get_/is_/set_ accessor forwarding at all (no
`get_`/`set_` name synthesis outside lint rules); the only documentation is the
`classes_spec` "Auto-Forwarding Properties" rows, which call `get_x()`/`set_x()`
explicitly. So there is nothing to match yet; the seed now defines the
semantics (get_ > is_ > no-paren for reads, set_ for writes, real field first,
undefined field = error). Porting them to the self-hosted compiler is open work.
