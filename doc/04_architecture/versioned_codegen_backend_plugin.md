# Versioned LLVM/Cranelift backend plugin architecture

<!-- codex-architecture -->

## Context

The compiler already owns `Codegen`, `BackendKind`, backend selectors, and
factories under `src/compiler/70.backend/backend/`. LLVM and Cranelift remain
statically coupled at several caller and SFFI sites, and Phase 3 linking can
select a compiler without admitting the matching `rt_cranelift_*` provider.

## Decision

Use an Adapter plus versioned provider ABI. Keep `Codegen` as the internal
pure-Simple semantic contract. Add a concrete plugin boundary that never passes
Simple trait objects or heap graphs across a shared-library ABI.

The shared contracts are:

- `BackendPluginRequestV1`: role, backend name, target, CPU/features,
  optimization policy, MIR ABI digest, and required capabilities.
- `BackendPluginDescriptorV1`: ABI/version/size, provider identity/build ID,
  supported roles/targets/capabilities, and a vtable.
- `BackendPluginVTableV1`: open session, compile module, finalize object,
  execute, retrieve diagnostics, and close session.
- `BackendSession`: admitted descriptor plus opaque provider-owned handle.

Dynamic providers export exactly `simple_backend_plugin_v1`. Built-in LLVM and
Cranelift adapters return the same descriptor and use the same admission path.
The loader uses the canonical checked dynamic-library facade; raw `dlopen` and
`dlsym` remain inside its SFFI owner.

## Selection

`load_backend(request)` is the only startup entry. Interpreter/JIT requests
Cranelift by default; compiler/AOT requests LLVM by default. `--backend` changes
the requested name. `--backend-plugin` optionally supplies a library path.
Explicit or default selection failing admission returns an error and never
silently switches providers.

## Layering

- `00.common`: ABI-safe request, descriptor metadata, errors, receipt schema.
- `70.backend`: loader, admission, session, LLVM and Cranelift adapters.
- `80.driver`: role-aware default policy and CLI parameter projection only.
- `95.interp`: requests an admitted session; no provider-specific calls.
- foreign provider libraries: implement only the versioned ABI.

## Cache and invalidation

Backend sessions are command-scoped. Descriptor metadata is cached by canonical
library identity plus file identity. Any library identity, build ID, ABI/MIR
digest, target, CPU feature, role, or optimization change invalidates compiled
artifact reuse.

## Consequences

One interface supports static and dynamic operation and prevents Phase 3 symbol
authority drift. The ABI requires explicit buffer ownership and versioning;
adding an operation needs a new compatible tail field or a new ABI version.

## Frozen C ABI v1 foundation

The normative foreign header is
`src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h`.
It fixes structure widths and sizes, pointer-plus-length borrowed inputs,
provider-owned outputs, and typed entry/open/compile/finalize/diagnostics/
close/release signatures. The library lease outlives every descriptor, vtable,
session, and buffer. ABI or structure mismatch fails before `open_session`.

This completes only the ABI foundation. Production descriptor decoding,
canonical MIR serialization, session integration, and `--backend-plugin`
activation remain pending.

Current status: native lifecycle, Simple canonical-MIR transport, CLI/cache
path policy, and provider-content identity are implemented. Interpreter extern
dispatch and admitted dynamic session activation remain pending. Phase 3
convergence is not established.
