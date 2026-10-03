# Checked Mach-O hosted dependency reader

Item4 hosted-linking prerequisite; not hosted executable completion or admission.
The existing static API remains explicitly freestanding. This module has no I/O,
environment access, loader execution, signature verification or publication.

`macho_read_dylib(bytes, target)` accepts thin little-endian 64-bit MH_DYLIB for
x86_64/arm64. It returns install name, packed current/compatibility versions,
platform/minimum OS/SDK metadata, dependency commands in ordinal order, and
exports with their flags, address, resolver, library ordinal and import name.
Reexport ordinals remain provider references: resolving dependency graphs belongs
to the future hosted request owner. Addresses are image virtual addresses, not
runtime-loaded addresses. TLS exports remain marked TLS; no TLS allocation occurs.

The reader validates command envelopes, strings within their owning commands,
segment and symbol table bounds, and bounded trie ULEB/payload/child records.
Trie traversal rejects cycles and repeated nodes, limits names to 4096 bytes and
export count to 1000000. The format is a tree; shared-node encodings fail closed.
Names are bounded ASCII; non-ASCII bytes fail closed pending a byte-string/UTF-8
contract. Unknown load-command payloads remain opaque and confer no capability.
LC_DYLD_EXPORTS_TRIE and LC_DYLD_INFO_ONLY export regions are supported; conflicting
declarations fail. A checked external-definition symbol table is the fallback
when no trie exists. Indirect symbol aliases fail closed pending alias contracts.

Tests use real clang objects and ld64.lld dylibs plus independent wire mutations.
Test execution is pending an admitted pure-Simple runtime. Remaining hosted work:
provider closure/two-level resolution, stubs/GOT, bind/rebase/linkedit, loader
commands, TLS/unwind, code signing and actual Darwin loader qualification.

Primary format references: [Apple loader.h](https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/loader.h),
[LLVM MachO.h](https://llvm.org/doxygen/BinaryFormat_2MachO_8h_source.html).
