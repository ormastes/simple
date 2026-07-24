# Detail design: SimpleOS filesystem toolchain and servers

## Loader flow

1. Canonicalize and open the requested mounted path.
2. Read/validate ELF header and bounded program-header table.
3. For each `PT_LOAD`, validate offsets/sizes, allocate pages, zero BSS, and
   read file-backed bytes directly into mapped frames in bounded chunks.
4. Build argv/env/auxv, enter ring 3, and report the real exit status.

## Image flow

- Build target-native static Clang and Simple payloads.
- Size FAT/initramfs from payload totals plus filesystem overhead.
- Write the validated bytes to all canonical paths and record the target build
  stamp in `/SYS/SIMPLETOOL.SDN`.
- Reject text, marker, empty, unstamped, wrong-entry, host-target, or missing
  payloads before staging.

## Server flow

- HTTP scenario: boot, send `GET /health` and `GET /`, assert status/body.
- DB scenario: use the same boot HTTP listener, send three `POST /db` requests,
  and require create, insert, and the selected known value in one boot.

## Error handling

Every build/boot/check wrapper returns nonzero for missing media, stale build
stamp, target mismatch, short reads, malformed ELF/query, timeout, guest fault,
unexpected preload use, or missing response.

<!-- codex-design -->
## Stage 4 ModuleSurface detail

### Data

`ModuleSurface` stores source index, canonical path/module name, content
length/hash, ordered imports/exports, declaration-kind/name tables, and typed
surface dictionaries:

- callables: declared parameter/return types, flags, visibility, span;
- composites: kind, name, visibility, span, and only identity metadata read by
  cross-module resolution; fields, layouts, and methods are omitted;
- enums: ordered variants with payload types and struct-field defaults;
- traits: full trait declaration so imported default methods can lower;
- impls: owner/trait/type parameters/associated types and method signatures;
- constants: name, declared type, mutability, visibility, and fixed-address
  metadata, without the value expression.

Ordinary bodies, parameter defaults, field defaults outside enum variants,
constant values, docs, local-only domain/AOP/DI/arch/mock declarations, and
ordinary attributes do not enter the surface.

### Driver flow

`driver_streaming_surface_enabled` requires AOT, `--low-memory`, entry closure,
`SIMPLE_BOOTSTRAP_STAGE4=1`, and a non-VHDL backend.

1. Keep the existing source discovery, deduplication, ordering, and parse-error
   semantics.
2. Parse each unique physical source and extract one independently owned
   canonical surface. Register every module alias to that same surface, then emit
   `phase2:surface:file:released path=... seq=... heap_registry=...` after the
   rich Module has left retained compiler state.
3. Validate source index/path/module/length/hash before the second parse.
4. Parse and lower one Module to HIR against the complete surface map. Preserve
   shared lowered traits and current error aggregation, keyed by canonical
   trait origin rather than short name.
5. Retain HIR for method resolution, constant folding, effect/type/layout
   checks, monomorphization, and the existing MIR layout prepass.
6. After streaming HIR succeeds, call the existing source and AST eviction
   owners. Do not mutate source content per file or execute in dictionary order.

Parse errors fail immediately. Surface/source mismatch, missing imported
declaration metadata, or malformed release markers fail closed. Repeated
identical `module_name::trait_name` imports are idempotent cache hits; fail only
when that key resolves to conflicting source/fingerprint/declaration metadata.
`ModuleSurfacesByName` backs import, re-export, glob, sibling, enum, and trait
resolution for every HIR path. Non-streaming paths derive it from retained rich
modules without reparsing and otherwise keep the existing flow.

### Observability and limits

The release marker is emitted only after surface installation and rich-Module
scope exit. The real-closure gate validates and computes from the first 10
unique ordered post-release markers and
requires average retained growth `(heap10 - heap1) / 9 <= 25,000`
objects/file. It requests process-group termination immediately on marker 10
under a pre-calibrated memory cap and 90-second deadline; a raced later marker
is diagnostic, not failure. Early/malformed/duplicate markers before the first
ten fail. This is not a full bootstrap.
