# Mach-O provider-owned runpath discovery

2026-10-04; base `860b367839dbd6c6c7b0974c9505efacc013113d`.
Owner `/root/linker_research`, branch `work/item4-macho-rpath-docs-20261004`,
isolated worktree `C:/dev/simple-item4-stream-got-docs-20261004`; this document
is the sole owned file. Runtime owns provider retention and closure context,
root owns native lookup/planning, acceptance owns specifications. Sidecars N/A.
Simple execution remains UNRUN; no new runtime admission is inferred.

This extends `macho_provider_closure_2026-10-04.md` toward the retained full SDK
goal. It does not replace Darwin loader execution, weak binding, SDK directives,
full framework discovery, managed authority or five-host qualification.

## Research distinction

Link-time reexport discovery and dyld runtime loading are different operations.
Apple ld64 `Options::findFile` enumerates the requesting dylib's own runpaths.
It expands loader-relative entries using that provider's source path. By
contrast, dyld's loader walks an inherited load-chain stack of runpaths.
Implementing the linker does not imply implementing or certifying that loader.

Current LLVM main also tries command-line runtime paths after the provider's
paths and retries the requesting dylib after its umbrella. An older cached
excerpt omitted these branches; owner-only must not be described as universal
LLVM parity. The selected project profile follows the explicit owner rule and
does not borrow executable or ancestor runpaths. Output `-rpath` still controls
emitted runtime commands; it is not a substitute for provider metadata.

Inline precedence is also a stated project contract: stage3 indexes explicit
inline declarations before external lookup. Apple has a global inline catalog;
LLVM searches the current top-level document's children. Their external-path
precedence differs from this project's retained inline-first policy. No blanket
ld64/LLD equivalence is claimed.

## Frozen shared API

Append `rpaths: [text] = []` to `MachOProviderV1`, preserving old constructors.
Binary projection reads actual `LC_RPATH` commands after original dylib envelope
validation. TextAPI lowering retains selected V5 `rpaths`; V4 has no corresponding
schema field and must not acquire an invented one.

`MachOProviderRunPathV1` contains `path` and `owner_path`.
`MachOProviderResolveRequestV2` contains `install_name`, `requester_path` and
ordered `runpaths: [MachOProviderRunPathV1]`. The V2 callback signature is
`fn(MachOProviderResolveRequestV2, MachOProviderSearchV1) -> Result<MachOProviderSourceV1, text>`.
`macho_provider_closure_v2` retains the V1 constructor's roots, target, client,
search and limits arguments, replacing only its callback type. It returns the
same closure owner; the V1 constructor and callback contract remain available.
The native callback is `native_macho_load_provider_v2`.
Native planning selects V2; each graph request carries the requesting node's
metadata and actual source path, including an inline node's physical document.

Do not allow an install-name-only external cache hit to erase that context.
Distinct owners may resolve the same `@rpath` spelling to different files. Reuse
an identical resolved path; reject conflicting files claiming one install
identity. An explicit inline catalog declaration is distinct from an incidental
cached external identity. Cache keys and work charging must preserve that
distinction and deterministic root ordering.

## Lookup and parser contract

For provider runpaths, preserve declaration order. Expand `@loader_path` against
the directory of the runpath owner, and `@executable_path` against the actual
output directory; both bare tokens and slash suffixes are directory forms.
Normalize legitimate `..` components without escaping absolute roots. Keep
Windows drive/UNC handling separate from target POSIX install identities.

An absolute POSIX runpath is rerooted exclusively beneath an explicitly supplied
SDK root. Without that root, its declared absolute path is used directly; this
is explicit provider metadata, not an added implicit host-search fallback.
Explicit host drive/UNC paths remain host paths. Never retry the unrooted POSIX
path after a rooted candidate fails. Runpath provenance must equal the normalized
requester source path. Bare relative paths, recursive `@rpath` and unknown tokens
reject; there is no invented CWD or owner-relative base for plain relative text.
Mach-O metadata uses forward slashes, including explicit drive/UNC spellings;
backslashes in runpath metadata reject. Native owner and output filesystem paths
are normalized separately and may arrive with host-native separators.
Selected malformed files fail immediately; do not try the next path after reading
a bad candidate. Existing non-runpath dependency-search precedence is preserved.

`LC_RPATH` is command `0x8000001c`. Validate its command size, string offset,
in-command NUL terminator, nonempty decoded path and configured name limits.
Do not read through a following command to find a terminator. Retain path order
and owner provenance; path strings are not an authority or file-identity seal.

Runpath request construction charges the existing closure work quota; this API
adds no independently certified resource budget. Context-cache entries and
candidates remain subject to the existing source/edge/work limits.
File reads remain resident with the existing size
guards; none of these counters proves whole-process RSS or no-swap enforcement.

## Acceptance matrix

All cases trace to ITEM4-REQ-006/007, use production callbacks and real files,
and retain source review versus execution distinctions.

1. Actual binary `LC_RPATH` and target-scoped V5 provider paths select real leaf
   files for both CPUs; image bind names/direct root ordinals remain independent
   expected values.
2. Two providers in different directories share a path string but each expands
   its own loader-relative directory. Conflicting same-install-name files reject;
   a genuinely shared resolved file can be reused.
3. Ordered paths select the first available candidate; first selected malformed
   content preserves destination and cannot fall through to a valid later file.
4. Bare/suffixed loader/executable tokens, `../Frameworks`, explicit absolute SDK
   paths, Windows drive/UNC normalization and missing candidates have real file
   oracles. Nested/unknown tokens and unsupported relative bases reject.
5. Parent/output-only runpaths cannot satisfy a child lacking its own declaration.
   This checks the chosen linker policy, not runtime dyld inheritance behavior.
6. Malformed real load commands exercise short headers, invalid offsets, empty
   names and missing terminators, with guarded mutations and valid baselines.
7. V1 callback/constructor compatibility, inline precedence, context quotas and
   deterministic repeated resolution remain covered without fake provider data.

## Primary sources

- [Apple ld64 Options.cpp](https://raw.githubusercontent.com/apple-oss-distributions/ld64/main/src/ld/Options.cpp):
  `findIndirectDylib`, `findFile`, `hasInlinedTAPIFile`, `findTAPIFile`.
- [LLVM Mach-O InputFiles.cpp](https://raw.githubusercontent.com/llvm/llvm-project/main/lld/MachO/InputFiles.cpp):
  current `findDylib` and `loadReexport`, including runtime-path fallback.
- [Apple dyld Loader.cpp](https://github.com/apple-oss-distributions/dyld/blob/main/dyld/Loader.cpp):
  `forEachResolvedAtPathVar` and its runtime load-chain traversal.
- [LLVM TextStubV5.cpp](https://llvm.org/docs/doxygen/TextStubV5_8cpp_source.html):
  target-scoped runpath metadata.

Implementation and final test review evidence are recorded separately after
exact candidates exist. Full SDK compatibility and native host execution remain open.
