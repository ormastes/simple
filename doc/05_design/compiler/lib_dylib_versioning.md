# Library and Dynamic-Library Versioning: Design

Plan: `doc/03_plan/compiler/lib_dylib_versioning_plan.md`.

## Module

`src/compiler/80.driver/libver/` is pure Simple. It contains:

- `identity.spl`: the `LibIdentity` struct.
- `naming.spl`: file-name builders and parsers.
- `sidecar.spl`: SDN emit and parse.
- `admit.spl`: `LibHostReq`, `LibAdmit`, the `LibRefusal` enum and `libver_admit`.
- `cache.spl`: the cache-key component and the publish manifest.

It uses no `Any` and no inheritance.

## Admission flow

The checks run in a fixed order, and the first failing check gives the refusal reason:

1. sidecar present and well-formed;
2. name;
3. triple;
4. ABI major, then the window, then minor;
5. tier;
6. digest, or the `iface_parts` subset;
7. sha256.

For dylibs, the loader runs this check before it resolves the entry symbol. For static archives, the link step runs it before it passes the archive to lld. In both cases a refusal stops the operation, with `LibRefusal.name()` in the diagnostic.

## Cache key

`libver_cache_component(id)` is folded into the native build cache scope, so that a change in version, ABI, digest, producer, triple or tier can never reuse objects across artifacts.

## Deprecation

- **Support window.** The consumer accepts the current ABI major. It also accepts N-1 while `lib_versioning.sdn` lists that major under `deprecated_abi`, which lasts one minor release cycle.
- **After the window.** An N-1 artifact is refused with `AbiOutOfWindow`.
- **Minor versions.** Minor ABI bumps are additive only.

## Release publish

The rc pipeline calls `libver_publish_manifest`. Each versioned library and its `.lib.sdn` sidecar are published under `lib/simple/<triple>/`. The manifest lists each file name and sha256, sorted by file name.
