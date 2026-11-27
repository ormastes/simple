# Reflective field stores bypass array value ownership

Status: source repair and three regressions authored; execution pending. Depends
on the core array descriptor/value-place owner repair. This followup adds no W2
capability or runtime qualification.

Baseline `44b513f1483f2ec2ee52d353b7b7c53f2746524c` implements
`__traits("set_member", object, field, value)` by evaluating a raw object ValueId
and passing the incoming raw ValueId to `val_struct_set_field`. Class array fields
therefore alias the incoming array; a struct receiver reached through a shared
array can mutate the shared child without detaching its array ancestor.

The setter now freezes its receiver path once, evaluates field and incoming value
in the original order, snapshots the incoming value, then resolves ancestor
uniqueness immediately before the field store. Class references retain identity.
Wrong receiver kinds produce a core error instead of indexing the struct arena.
Absent field behavior remains the existing setter no-op.

`core_array_cow_traits_spec.spl` executes actual parsed source through
`core_jit_interpret(..., 999999)` (JIT disabled). Its three cases check class field
array isolation plus class identity, nested value-struct array detachment, and
receiver/field/incoming callback counts with an ancestor snapshot created by the
last callback. No copied template or manually fabricated guest AST substitutes
for the source call.

No Simple compiler, SSpec or runtime execution has run. Qualification requires
the admitted self-hosted producer, exact source/runtime/backend/target and an
isolated frozen-owner build. Source review/whitespace are separate evidence.
The prior sixteen-path core repair freeze is unchanged; this is a separate
three-path dependent followup. MIR/native/JIT and W2 remain unadmitted.
