# Mach-O provider closure and direct access

2026-10-04; base `9f4a7c01a0dbe2cd0bb83b9bc4980ad1cbf126e5`.
Owner `/root/linker_research`, branch `work/item4-macho-closure-docs-20261004`,
worktree `C:/dev/simple-item4-stream-got-docs-20261004`. This file is the sole
owned path. Runtime owns graph/hosted integration, acceptance owns real fixtures
and specifications, root owns native planning/file lookup and final integration.
Sidecars N/A. Source review, external fixture evidence and Simple execution are
separate; Simple execution and native qualification remain UNRUN.

This continues the four-stage SDK plan in `macho_sdk_providers_2026-10-04.md`.
It does not replace SDK binding, loader execution, managed authority, bounded
worker enforcement or the five-host requirements with metadata parsing.

## Local production boundary

The current native adapter reads selected binary or TextAPI provider files and
passes typed metadata to `macho_hosted_link_with_providers`. Hosted slots search
direct provider exports; fixups emit each selected library's direct ordinal.
Current leaf lowering rejects whole-library closure, access restrictions and
symbol reexports. Binary projection already preserves ordered dependency
commands and explicit export aliases, without provider VM addresses.

The new boundary must preserve that direct ordinal ordering while retaining a
graph of reachable provider identities. Query the graph for an unresolved
symbol; do not flatten every dependency into a new executable load command.
The file adapter remains the owner of external reads and output publication.

## Frozen shared contract

`provider_closure_types.spl` exports:

- `MachOProviderSourceV1 {path: text, bytes: [u8]}`.
- `MachOProviderSearchV1 {sdk_root: text, library_paths: [text], output_path: text}`.
- `MachOProviderClientV1 {output_install_name: text, client_name: Option<text>,
  parent_umbrella: Option<text>}`. Signing identifiers are excluded.
- `MachOProviderClosureLimitsV1 {max_sources, max_total_bytes, max_edges,
  max_symbols, max_work, max_depth}`; all counters are `i64`.
- `MachOProviderBindingV1 {root_ordinal: i64, name: text, flags: i64}`.
- `macho_provider_closure_default_limits_v1()` returns defaults of 4096 graph
  sources, 64MiB input bytes, 65536 edges, 1000000 symbols, 10000000 work units
  and depth64. Inline graph nodes count toward max_sources.

`provider_closure.spl` exports `macho_provider_closure_v1(roots, target,
client, search, load, limits) -> Result<MachOProviderClosureV1, text>`, where
target is `MachOTbdTargetV1` and `load` is
`fn(text, text, MachOProviderSearchV1) -> Result<MachOProviderSourceV1, text>`.
The callback receives install name, requesting source path and explicit search
context, avoiding captured mutable lookup state. The owner provides
`direct_providers()`, `me resolve_import(name) -> Result<Option<MachOProviderBindingV1>, text>`
and `validate_for_request(arch: RelocArch, minimum_os) -> Result<bool, text>`.
Mutation occurs through the owner method so lookup work charging is retained.

`macho_hosted_link_with_closure(objects, archives, closure, request)` validates
reachable deployment constraints then consumes actual resolution results for
slots, fixups and image metadata. Direct provider ordering remains observable
through emitted load commands. Existing typed/byte entrypoints preserve their
defaults. No API returns a guessed provider VM address.

Inline interfaces resolve before external lookup. The selected provider must
match the requested install name and target; a same-basename file is not proof.
External reads use explicit SDK/search ownership, never an implicit host SDK or
dyld-cache assumption. Missing, conflicting or malformed selected input fails
before publication. Closure values are caller-trusted in-process metadata, not
authenticated capabilities or managed-runtime admission.

The external callback needs requesting source path plus explicit search context,
not only install name: `@loader_path` refers to that source's directory, while
`@executable_path` refers to the actual output directory. SDK lookup maps an
absolute install path under the explicitly supplied SDK root. Configured library
search is deterministic, and a selected malformed file cannot trigger fallback.
Provider `@rpath` is explicitly unsupported in this profile until its own
retained runpaths are modeled; reject rather than borrowing executable rpaths,
CWD or signing metadata. Dependency candidates probe TextAPI before binary;
existing direct library search order remains unchanged. Configured search paths
precede SDK-root mapping, with no implicit host SDK or host filesystem fallback.
Normalize legitimate `@loader_path/../Frameworks` paths using actual host path
rules; avoid double-prefixing Windows drive-absolute paths. SDK install-path
mapping must not accidentally escape its configured root. Lexical normalization
does not establish filesystem identity or trust.
Reachable providers must satisfy output target/deployment requirements; unrelated
inline libraries need schema validation but not the output's deployment test.

## Reexport and alias semantics

Whole-library reexports search a provider's own exports before its reexport
edges in deterministic order. Ordinary dependency commands are not whole-library
reexport edges. An explicit binary export alias follows its original one-based
dependency ordinal and imported name internally; the emitted executable bind
keeps the original outward symbol and direct root ordinal. The loader performs
the alias traversal. Preserve dependency ordering, including non-reexport
commands, because those commands still occupy ordinal slots.

TextAPI `reexported_symbols` are explicit root-visible symbol declarations with
no per-symbol dependency ordinal or alias target. Do not invent these missing
fields. Whole-library `reexported_libraries` separately names graph edges.
Selected weak/absolute semantics remain subject to the hosted implementation's
actual support; discovering an unsupported export must not silently regularize
it. Unused unsupported export metadata can remain metadata.

Cycles are not automatically malformed. Bound traversal with visited
`(provider identity, requested symbol)` pairs; aliases can change the name while
remaining within the same provider graph. A cycle with a reachable definition
must resolve; a closed alias cycle must terminate without a fabricated binding.
An unsuccessful alias branch returns no match to its parent traversal; it must
not abort a later sibling reexport edge that can provide the requested symbol.
Unmodeled legacy `LC_SUB_UMBRELLA`/`LC_SUB_LIBRARY` semantics must explicitly
reject until implemented rather than disappear during binary projection.

## Permission identity

Apple's open-source linker checks restrictions when a dylib is directly linked.
Its rules allow a matching output parent, a sibling with the same declared
umbrella, or a permitted client. Client identity comes from explicit
`-client_name`, otherwise a normalized output install/path leaf (remove `lib`
and variant/version suffix beginning at the first underscore or dot). Its
allowable-client comparison is exactly `allowable.starts_with(effective_client)`.
Empty derived identities must not become universal matches. These are output
semantics, not signature identity. Native execution plans store explicit
`-client_name`, but use the actual file-link call's output path, not a stale
planning path. The native executable grammar does not accept `-umbrella`;
generic caller context can represent that relationship explicitly.
Convert directory separators for cross-host output identity, but preserve its
actual spelling (including `./`) for the source-defined parent/slash condition.
Filesystem canonicalization is a separate operation.

An executable linking through an allowed umbrella does not need to appear in
every transitive leaf's client list. Conversely, explicitly naming a restricted
leaf remains a direct-access check even when another root also reexports it.
Parent metadata alone does not authenticate the caller. The implementation
profile must state which output kinds and parent/sibling cases are representable;
do not accept a claimed dylib identity for an executable accidentally.

## Acceptance obligations

All scenarios trace to ITEM4-REQ-006/007 and use real file or typed production
entrypoints, canonical `std.spec.step`, and independent image oracles.

1. Both formats/CPUs: root to inline middle to actual external leaf; inspect
   bind name/ordinal and direct load commands, not only parse success.
2. Binary alias: renamed leaf lookup succeeds while root outward name and
   ordinal remain on the emitted bind stream; ordinary dependencies retain
   their ordinal positions.
3. Cyclic graph with reachable definition succeeds; alias-only cycle,
   missing dependency/target and conflicting identities terminate with errors.
4. Direct client denied/allowed and parent/umbrella cases use actual output
   identity; changing only signing identifier cannot grant access. Indirect
   restricted leaf remains usable through a valid root.
5. Multiple roots preserve deterministic precedence and root ordinals; adding
   an unused transitive provider does not invent an executable direct load.
6. Real SDK-root/search fixtures exercise inline precedence, exact identity,
   malformed selected input, logical limits and unchanged destination sentinels.

Graph caching and visited-state bounds control repeated lookup work. They are
not hard RSS, no-swap, descendant containment or performance qualification.
Each active node validates metadata and builds an export-name index once, with
explicit owner writeback and charged construction. Queries use that index;
binary expansion builds an alias-ordinal set once instead of scanning every
export for every dependency. A single mutable lookup owner retains cumulative
work across all unresolved symbols in one hosted job. Parser-declared symbol
counts include unselected metadata; expanded ObjC exports have their own cap
under the same configured symbol maximum. Duplicate direct roots and conflicting
source install identities reject rather than silently changing load ordering.
Representative SDK closure timing and peak-memory measurements remain required
after runtime admission; do not infer them from small authored fixtures.

## Primary evidence

- [Apple ld64 InputFiles.cpp](https://github.com/apple-oss-distributions/ld64/blob/main/src/ld/InputFiles.cpp):
  `markExplicitlyLinkedDylibs` and `checkDylibClientRestrictions` define the
  direct-access boundary and output/client/umbrella alternatives.
- [LLVM DriverUtils.cpp](https://github.com/llvm/llvm-project/blob/main/lld/MachO/DriverUtils.cpp):
  direct client checks and an explicit compatibility caveat about parent/sibling
  behavior. LLVM success alone is not proof of all Apple access semantics.
- [Apple dyld Loader.cpp](https://github.com/apple-oss-distributions/dyld/blob/main/dyld/Loader.cpp):
  export aliases follow dependency ordinal/import name; symbol changes require
  a fresh search state. Static lookup follows reexports, not arbitrary loads.
- [LLVM TextStub.cpp](https://www.llvm.org/docs/doxygen/TextStub_8cpp_source.html)
  and [TextStubV5.cpp](https://llvm.org/docs/doxygen/TextStubV5_8cpp_source.html):
  separate per-symbol reexport declarations and whole-library metadata.

Exact implementation review evidence will be recorded when candidates exist.
No release or complete SDK claim follows this design.
