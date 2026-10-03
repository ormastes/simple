# Hosted Mach-O image construction lane

Scope: item4 dyld-loaded executable generation; separate from static LC_UNIXTHREAD
images and dependency inspection. SSpec/runtime evidence is **UNRUN**. Sidecars N/A.

API: `macho_hosted_link(objects, archives, providers, request)` returns image bytes.
`MachOHostedRequest` carries target, entry, packed macOS minimum/SDK versions,
maximum image bytes, signing identifier and explicit runtime rpaths. Providers are explicit ordered dylib
bytes; no implicit filesystem, SDK, environment, subprocess or path search.

The first coherent slice emits a two-level PIE MH_EXECUTE: LC_MAIN,
LC_LOAD_DYLINKER, ordered LC_LOAD_DYLIB, build version, four segments including
LINKEDIT, eager pointer bind streams and local pointer rebase streams. Calls use
architecture-specific indirect stubs, GOT references use writable pointer slots.
No lazy-binding helper is required. Regular data imports require GOT or pointer
relocations: direct PC-relative dynamic data cannot silently become a local address.
Ad-hoc SHA-256 CodeDirectory construction is distinct from signature validation.
LC_UUID derives deterministically from the unsigned image with UUID bytes zero.
LC_MAIN always declares `/usr/lib/libSystem.B.dylib`, reusing an explicit provider
or appending its runtime-only load command after all provider ordinals. This does
not supply SDK exports or certify the target host's libSystem identity.

Imported TLV descriptors are supported through actual x64 TLV and ARM64 TLVPPAGE
relocations into eagerly bound slots. Descriptor/template allocation and per-thread
initialization remain owned by the dylib; local TLS definitions fail explicitly.

Hosted fixups extend the shared relocator only through explicit per-site target
maps; static callers retain their rejection behavior. Segment/page/budget bounds
are checked before allocation. Missing providers, incompatible CPU/platform,
unsupported TLS/unwind/initializers or unsupported weak/coalescing semantics fail.

Completion matrix (source implementation is not execution evidence):

| Gate | State |
|---|---|
| Entry/loader/load-dylib/build/rpath/UUID commands | IMPLEMENTED; tests UNRUN |
| Eager binds, GOT, call stubs, pointer rebases | IMPLEMENTED x64/arm64; tests UNRUN |
| Ad-hoc signature wire construction | IMPLEMENTED; independent zero-page vector authored, UNRUN |
| Imported TLV descriptor bindings | IMPLEMENTED x64/arm64; real fixtures, tests UNRUN |
| Reexport provider closure, weak interposition | OPEN |
| Local TLV descriptor/template/initializer support | OPEN; explicit rejection |
| Compact unwind / DWARF personalities and exceptions | OPEN |
| Native Darwin execution/signature qualification | UNRUN |
| SSpec/docgen/maintain/core/MCP smoke | UNRUN: admitted runtime unavailable |
| ARM64 ADDEND hosted pairing / executable dynamic exports | OPEN; explicit rejection / no exports contract |
| Runtime-discovered Objective-C/Swift/custom section metadata | OPEN; unrecognized section names explicitly rejected |

Performance qualification is also UNRUN. Arrays are preallocated for image/page
hash storage; stream construction remains bounded by admitted input and import
counts. The existing SHA helper materializes an i64 copy for UUID hashing; its
peak memory is not claimed to equal the output-image budget or job limit.

Primary references: [Apple loader.h](https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/loader.h),
[Apple dyld Loader.cpp](https://github.com/apple-oss-distributions/dyld/blob/main/dyld/Loader.cpp),
[LLVM ARM64 signature implementation review](https://reviews.llvm.org/D96164).
