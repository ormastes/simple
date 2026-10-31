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
- Structs keep value semantics: they are deep-copied in both directions.
- Classes keep reference semantics. The object has one hidden trailing slot
  holding an identity token that is never reused, mapped to a
  `Weak<ClassInstance>`. While the instance is alive, decoding returns the
  same `Arc`. If it has been dropped, a new instance is rebuilt from the
  native fields and bound to the token. Identity is keyed by token rather
  than heap address because transient heap scopes free addresses and reuse
  them. The registry stores only `Weak`s and prunes dead entries, so it never
  keeps an instance alive.
- Cycles and aliasing are handled with a memo that lives for one crossing and
  is cleared when the outermost crossing ends, including on unwind. An object
  is allocated and memoized before its fields are filled, so a self-reference
  terminates and two aliases of one instance become one native object.
  Decoding mirrors this.
- Known limit, by design: the interpreter instance is authoritative. A write
  made natively through `rt_object_field_set` to a live instance's object is
  not merged back, because merging would overwrite interpreter-side
  mutations made during nested calls. Compiled code does not use
  `rt_object_*` for its own structs (`StructInit` lowers to raw `rt_alloc`
  aggregates), so the bridge object is opaque to native code: native code can
  hold it and pass it back, but cannot read its fields by offset.
- `Value::TraitObject` still marshals to nil, now through an explicit arm,
  because the layout does not carry the trait name.
- Separate pre-existing gap (not changed here): `runtime_to_value` has no
  `HeapObjectType::Enum` decoder, so an enum inside an object (or anywhere)
  still decodes to nil on the way back into the interpreter.

**Tests.** Rust unit tests in `runtime_bridge.rs` (`cargo test -p
simple-compiler --lib runtime_bridge`): struct round trip with nested
array and dict fields, struct copy semantics, class identity and later
mutation, a dropped instance rebuilt and rebound, a self-cycle, two aliases
becoming one object, class inside struct and struct inside class, and
foreign or unregistered class ids decoding to nil. A `.spl` interp <-> JIT
spec was not added: the hybrid transform does not route class-typed values
through InterpCall in a way a spec can pin today, and compiled code cannot
read the bridge object's fields.

No `@workaround` tag referenced this defect. The interpreter lock
side-table in `interpreter_extern/atomic.rs` (`PROTECTED_VALUES`) is still
needed for closures, so it stays. Its comment was updated.
