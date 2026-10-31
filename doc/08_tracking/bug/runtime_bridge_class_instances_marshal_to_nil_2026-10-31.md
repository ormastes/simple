# Struct values and class instances became nil at the interp <-> JIT bridge (2026-10-31)

## Resolved 2026-10-31

**Symptom.** A struct value (`Value::Object`) or class instance
(`Value::ClassInstance`) that crossed `rt_interp_call` / `rt_interp_eval`
(an argument passed from compiled code into the interpreter, or a result
handed back) arrived on the other side as `nil`. Dict, enum and packed-byte
values had each been fixed individually; objects had not.

**Root cause.** `src/compiler_rust/compiler/src/runtime_bridge.rs`:
`value_to_runtime` had no arm for `Value::Object` / `Value::ClassInstance`
and fell through to `_ => RuntimeValue::NIL`; `runtime_to_value` had no arm
for `HeapObjectType::Object` and fell through to its `_ => Value::Nil`
fallback. A native `RuntimeObject` carries only a class id and positional
fields, so there was also nothing to recover the class name or field names
from.

**Fix.** New `object_bridge` module in `runtime_bridge.rs`:

- Objects marshal to a `RuntimeObject` (`rt_object_new`). Its class id
  (>= `0x7000_0000`, a range only the bridge allocates) names a layout in a
  process-global registry: class name, field names in sorted order, and the
  interpreter carrier (struct or class). If the id is not registered, or the
  field count does not match the layout, the object decodes to nil as before,
  so a foreign RuntimeObject is never misread.
- Value semantics for both structs and classes. Classes are value types
  (`doc/07_guide/language/capability_library_authoring.md`;
  `doc/08_tracking/bug/jit_class_instances_alias_instead_of_copy_2026-09-27.md`),
  so every crossing makes a deep copy in both directions. A mutation on
  either side after the crossing is not visible on the other side. A native
  `rt_object_field_set` is visible in the copy decoded from that object.
  There are no identity tokens and no instance registry, so nothing is kept
  alive and the result does not depend on timing. Two equal copies compare
  equal under native structural equality (`sffi/equality.rs` `object_eq`:
  same class id and same fields).
- Cycles and aliasing are handled with a memo that lives for one crossing and
  is cleared when the outermost crossing ends, including on unwind. An object
  is allocated and memoized before its fields are filled, so a self-reference
  terminates and two aliases inside one value become one native object.
  Decoding mirrors this. Two separate crossings are two copies.
- Registry bound: there is one layout per distinct (class name, field-name
  set, carrier). Field sets are fixed by the type definitions, so the count
  is bounded by the program's types. A hard cap (`MAX_LAYOUTS` = 65536)
  backstops it: a new layout beyond the cap marshals to nil, as before this
  fix.
- Compiled code does not use `rt_object_*` for its own structs (`StructInit`
  lowers to raw `rt_alloc` aggregates), so the bridge object is opaque to
  native code: native code can hold it and pass it back, but cannot read its
  fields by offset.
- `Value::TraitObject` still marshals to nil, now through an explicit arm,
  because the layout does not carry the trait name.
- Separate pre-existing gap (not changed here): `runtime_to_value` has no
  `HeapObjectType::Enum` decoder, so an enum inside an object (or anywhere)
  still decodes to nil on the way back into the interpreter.

**Tests.** Rust unit tests in `runtime_bridge.rs` (`cargo test -p
simple-compiler --lib runtime_bridge`): struct round trip with nested
array and dict fields, struct copy semantics, class copy and later
mutation (copy semantics, native write visible after decode, original
unchanged), native structural equality of two copies, round trips from two
threads, a self-cycle, two aliases
becoming one object, class inside struct and struct inside class, and
foreign or unregistered class ids decoding to nil. A `.spl` interp <-> JIT
spec was not added: the hybrid transform does not route class-typed values
through InterpCall in a way a spec can pin today, and compiled code cannot
read the bridge object's fields.

No `@workaround` tag referenced this defect. The interpreter lock
side-table in `interpreter_extern/atomic.rs` (`PROTECTED_VALUES`) is still
needed for closures, so it stays. Its comment was updated.
