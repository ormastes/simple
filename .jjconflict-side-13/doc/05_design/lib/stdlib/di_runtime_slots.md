# DI Runtime Slots

FR-PLUG-0005 adds an explicit runtime-slot index beside the existing string-keyed DI runtime. Static DI remains the default path. Plugin-backed implementations are accepted only for declared runtime slots.

## Design

- `DiRuntimeSlot` declares a slot name, expected type, collection behavior, and final-binding guard.
- `DiRuntimePluginBinding` models the trusted plugin/SMF loader handoff: slot name, type, plugin name, safe relative library path, implementation symbol/class, and deterministic order.
- `di_runtime_build_slot_index(...)` performs startup validation once and stores valid bindings in deterministic order.
- `di_runtime_resolve_indexed(...)` resolves scalar or collection slots from the prebuilt index and returns typed diagnostics for missing, duplicate, undeclared, unsafe, or final bindings.

## Security

Bindings reject undeclared slots, type mismatches, final runtime slots, absolute paths, parent traversal, home-relative paths, backslashes, URL-like paths, and empty plugin or implementation identifiers.

## Performance

The index records `startup_scan_count` as validation work and `hot_resolve_count` as per-resolve slot matches. Hot resolution does not reread SDN, traverse the filesystem, or perform global reflection.
