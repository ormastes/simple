# Versioned codegen backend plugin detail design

<!-- codex-design -->

## Data model

`BackendRole` has `InterpreterJit` and `CompilerAot`. `BackendCapability`
includes JIT execute, object emit, debug info, optimization, cross-target, and
incremental compilation. `BackendPluginError` distinguishes not found, load,
symbol, ABI, MIR digest, capability, target, provider, and teardown failures.

All cross-library strings and buffers use pointer-plus-length borrowed inputs or
provider-owned result buffers paired with an explicit release operation. No
exception/panic, Simple object, Rust object, collection, or allocator ownership
crosses the boundary.

## Startup flow

1. Driver creates `BackendPluginRequestV1` from role and parameters.
2. Registry resolves a built-in descriptor or canonical dynamic-library path.
3. Loader obtains `simple_backend_plugin_v1` through checked dynamic loading.
4. Admission validates structure size, ABI, provider version, MIR digest,
   requested role, target, and capabilities.
5. Vtable `open_session` returns an opaque handle.
6. `BackendSession` owns handle, library lease, diagnostics, and receipt facts.
7. All MIR compile/finalize/execute calls route through the session.
8. Close releases provider objects before the library lease.

## Defaults and parameters

- Interpreter/JIT: `cranelift`; `--backend=llvm` selects LLVM.
- Compiler/AOT: `llvm`; `--backend=cranelift` selects Cranelift.
- `--backend-plugin=PATH` selects a dynamic provider implementation.
- Environment projection is allowed only at the driver owner and is copied into
  the immutable request; provider code does not read environment variables.

## Diagnostics and observability

Test/debug diagnostics record resolution, load, admission, session-open, first
compile, finalize/execute, and close durations; provider name/version/build ID;
and rejection reason. Normal output remains quiet.

## Compatibility

Existing `CodegenFactory` creation is wrapped first. LLVM and Cranelift adapters
translate the common request/session operations into current APIs. Direct
provider calls are removed only after equivalence tests pass.

## Error rules

No implicit backend substitution. No partially emitted output survives an
admission or compile failure. Teardown runs once, and a teardown diagnostic does
not replace the primary compile error.

## C ABI v1 wire and ownership contract

The complete request packet uses `SBQ1` magic, schema1 and ABI1, followed by
role/capabilities and six length-prefixed fields: backend name, target, CPU,
features, optimization and MIR ABI digest. Features use a u32 item count and
u32 length per UTF-8 item, preserving order and embedded delimiters. The packet
header is48bytes; total size is at most64KiB. Text/item lengths are at most4KiB,
feature count128 and feature section32KiB. Only CPU may be empty to explicitly
request the provider default. Required text is nonempty, strict UTF-8 and NUL-free.
Unknown schema/ABI/role/capability bits, truncation and trailing bytes are rejected
before provider loading. The incomplete historical16byte packet is unsupported.
Plugin path remains a local selection field, separate from provider configuration.

Pure-Simple transport owns encoding and roundtrip validation. Runtime ABI glue
decodes bounded borrowed slices without heap allocation; providers must copy
configuration they retain after open_session returns. Single/batch release and
borrowed-library lifetime are unchanged. This does not implement production
provider descriptors, full MIR fidelity or dynamic loader completion.

`simple_backend_plugin_v1()` returns a borrowed immutable descriptor. Every
structure begins with `abi_version` and `struct_size`, validated before its tail
is read. Text and MIR inputs are borrowed byte slices valid only during a call.
Compile, finalize, and diagnostics outputs are provider-owned
`(data,size,owner_token)` buffers released exactly once through the same
vtable. Consumers release buffers, close the session once, then unload the
library. Native lifecycle, Simple canonical-MIR transport, CLI propagation,
and cache path/content identity are implemented. Interpreter dispatch and the
dynamic session adapter remain open; Phase 3 convergence is unproven.
