# SCV dynamic Wasm boundary

Status: typed bridge contract tested; whole-runtime and Phase2 qualification pending.

The Wasm executor previously probed a dynamic provider but called static
wasm_rt_* externs. Runtime availability checks cannot satisfy those native link
requirements. Bind the three functions from one DynLib and retain its mapping
through one typed transaction instead of linking a design-only provider shim.

The native boundary calls the exact provider signatures:

| Function | Provider ABI |
|---|---|
| wasm_rt_load | const char* -> int64_t |
| wasm_rt_parse_all | int64_t, const char*, int64_t -> const char* |
| wasm_rt_free | int64_t -> void |

Integer-only dynamic dispatch is not a substitute for void or pointer-return
calls. The bridge accepts raw function addresses and borrowed byte ranges;
Simple retains the source texts while the bridge copies input into stable,
NUL-terminated allocations. Grammar paths reject embedded NUL. Source lengths
remain byte lengths and may include embedded NUL. Bounds are 1 MiB for the
grammar path, 16 MiB for source and 64 MiB for returned text.

After a successful positive load handle, free is called exactly once, including
parse/null/output/allocation failures. Output bytes are copied before free
invalidates the provider pointer. Simple copies the owned bridge buffer into
text and releases that buffer before ending the DynLib lease and closing the
mapping. Missing symbols, failed leases or an empty result cannot acquire a
successful Wasm parse label. Existing caller artifact/hash/span checks remain.

runtime_contracts.c includes the bounded runtime owner, keeping existing core-C
bundle rosters consistent. This repairs a proven native ABI gap below the
Simple dynamic-library facade; it does not add a fake Wasm implementation or
install/qualify wasmtime. Real-provider parsing remains separate evidence.

The GNU contract harness uses exact typed callback fixtures and mocked runtime
allocation. Its instrumented run passes normal, bound, copy-before-free and
allocation-failure paths with 100% line and 81.25% branch coverage of the bridge
source. That is standalone bridge evidence, not whole-runtime, interpreter,
cryptographic provider admission or compiler qualification.
