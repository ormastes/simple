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

## Native probe exposed a second, blocking transport defect

The original typed-local fixture reached MIR and emitted COFF object
`aot-aba7a9d34c45a5db3264ca916a65dd2ba8ef603b04f9858a290dbb483149543a.o`
(SHA256 `38fa4907d1139029186925296e0a45d075472682323210726cce321c7a42a10c`).
After manual linking against the pinned archive, it returned 2: present-key
lookup failed. This is **not** a passing annotation fix.

Object disassembly shows `check_keys` calling `rt_interp_cstr` before the
text-key lookup and passing the integer key directly without
`rt_value_int_wide`. Insertion instead creates a tagged string and boxes the
integer. The generic extern declaration therefore selects ordinary FFI
transport rather than the dictionary owner's tagged-value key transport.
The unchanged C lookup baseline passes; changing its hash/equality algorithm
would not repair these incompatible arguments.

The revised probe uses `.contains_key` on explicitly typed `Dict` parameters.
The shared MIR dictionary method path calls `lower_dict_key`, which invokes
`box_runtime_value`, matching insertion. This route is being validated before
production callers are changed. A bare class-field method replacement is
insufficient: missing receiver type metadata can route it incorrectly, so any
workaround must retain a concrete dictionary receiver type too. Native and
cross-platform qualification remain pending.

## Shared compiler repair under review

`HirFunction.extern_runtime_value_abi` records declaration provenance: zero is
the unchanged raw C ABI, one admits a semantic dictionary key, and two admits
an identity-sensitive runtime root. Only specialization of an original generic
extern with the exact runtime signature creates a nonzero value. Both parsed
`Named` binder symbols and canonical `TypeParam` binders are checked against
the declaration. A concrete fixed-i64 prototype is never inferred to be a
semantic facade merely because its C name matches.

The field survives the versioned HIR codec, semantic reconstruction, archive
signatures, and ABI interface fingerprints. Common MIR validates the admitted
declaration, uses physical i64 argument words, and normalizes C int8_t results
to Bool. Dictionary keys use the existing RuntimeValue boxing owner. Root
operations suppress text-to-C-string conversion and retain heap owner words;
semantic primitive values are boxed so an integer such as 17 cannot be mistaken
for a pointer. Raw fixed-i64 prototypes remain untouched.

The authored provenance spec covers parsed declaration admission, integer
specialization, archive metadata, codec roundtrip, raw overload exclusion,
unknown-mode rejection, and physical return width. The original raw generic
native regression is retained as `runtime_generic_extern_abi_native.spl`;
the dictionary-method fixture is a separate current-producer diagnostic.
No runtime or cross-platform PASS is claimed for the new compiler repair.
The generated codec field update is mechanical and still requires comparison
with the canonical `compiler_schema ... codec` regeneration under admitted
pure tooling before completion. HIR codec v14 deliberately rejects older
serialized layouts; old HIR receipts are not transplanted into this schema.

## Focused compiler-owner harness: return-only generic projection blocker

The first native harness attempt using producer `76c04806d8321705424b7ebbf11ddfbe5726771ad4033696d4b308c24e8d33fd` and candidate `63007bc614eac1d251d59f1cae9ca7c76f63921c` failed at monomorphization, before any object or fixture execution. All 12 unresolved call sites were specializations of the same call at `70.backend/backend/_MirToLlvm/core_codegen.spl:173`: `_sffi_tuple_get<T>` called return-only generic `rt_tuple_get` without explicit type arguments. The MIR shard and fallback worker each reported those 12 sites; they are not 24 distinct source defects.

The backend now matches the existing MIR-expression owner: declare the nil-capable runtime projection as `rt_tuple_get<T>(...) -> T?` and forward `<T>` explicitly. The C implementation returns nil for missing or out-of-range slots. No monomorphization check is disabled. The added native fixture checks a retained record payload and negative/upper-out-of-range slots; execution is pending. The provenance spec title now accurately describes admission checks rather than claiming runtime identity coverage.

Evidence: `C:/dev/runtime-value-abi-focused-20261030/attempt1/{stdout.log,stderr.log,result.sdn}`. Original artifacts are preserved. This blocker does not qualify or disprove the new runtime-value ABI lowering; the compiler harness itself did not finish building.
Review caught an invalid initial test assumption: newly allocated tuple slots contain raw zero, whereas the runtime nil tag is distinct. The regression therefore tests the documented invalid-index nil branch, not unspecified unset-slot contents. No runtime initialization behavior was changed.
