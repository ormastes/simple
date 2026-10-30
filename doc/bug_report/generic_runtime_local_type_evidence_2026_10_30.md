# Generic runtime calls lose local type evidence

Status: open; source annotation workaround pending native validation.

The b81f148 Phase3 attempt2, using pure producer SHA256
76c04806d8321705424b7ebbf11ddfbe5726771ad4033696d4b308c24e8d33fd,
exited 1 at 2026-10-30T04:30:33Z after all 1604 HIR modules completed.
Its stdout records 24 E-MONO-032 diagnostics: 17 dictionary contains,
four transient promotions, two enum discriminants, and one heap-reference
formation probe. These represent 20 distinct source locations; two VHDL
locations are each reported three times. Every diagnostic reports argument
inference having no concrete local type. This is not a missing native export.

`collect_lets_stmt_invocation_inner_v1` admits concrete source annotations
into the mono environment. The workaround supplies the actual declared
record-field or function-return type at each failing boundary. Generic FFI
adapters, key boxing, ownership operations, decoder checks, and runtime
implementations remain unchanged. The surface probe retains its original
nil short circuit. No global mono disabling or generic erasure is used.

`rt_dict_contains` already delegates once to `rt_core_dict_has`; the change
introduces neither a key scan nor a key copy nor additional boxing. All four
runtime symbols exist in the pinned native archive
5d7399d0c9c6b906b2981028c15185829ab35c960042bffb9d41e358ef8820e8.

Native regression input:
`test/01_unit/compiler/monomorphize/fixtures/runtime_generic_typed_key_native.spl`.
It checks empty dictionaries, present keys with zero/empty values, separate
text/integer missing keys, and 100000 repeated successful lookups. Compile
and run using the existing pure producer and runtime capsule; record exit,
elapsed time, and peak RSS. Runtime validation has not yet run. Compare the
same loop with direct typed parameter keys for a compatible performance
baseline; annotations themselves must not create a lookup allocation.

Resume only through genuine compiler cache identities and dependency closure.
Changed sources require fresh HIR and dependent MIR/object admission. Preserve
valid unrelated artifacts, but do not copy a terminal status to a new source
fingerprint. No C runtime or full bootstrap rebuild is required by this patch.
The underlying inference deficiency remains open after the annotation
workaround; canonical BugDB registration awaits an admitted full CLI.
