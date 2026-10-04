# Mach-O SDK providers: complete semantic path

Research/design dated 2026-10-04, base
`44b0d32606481ce7daf2d1971b0a973b5d065e60`.
Owner `/root/linker_research`; isolated branch/session
`work/item4-macho-sdk-docs-20261004`, worktree
`C:/dev/simple-item4-stream-got-docs-20261004`. Only this document is owned here.
Runtime owns source, acceptance owns tests, root owns integration and common
tracking. Sidecars N/A. Native and Simple runtime qualification remain UNRUN.

## Goal and present gap

SDK support means actual native-link requests can resolve platform-selected
provider contracts, enforce their restrictions, and emit correct load commands
and bindings. Parse success alone, V5 alone, fabricated Mach-O images, or guessed
system exports do not meet the goal. Both V4 YAML and V5 JSON remain mandatory.

Current `macho/dylib.spl` validates real thin MH_DYLIB images and exposes binary
export addresses. `hosted_fixups.spl` consumes export names/kinds but rejects
weak/reexport/absolute providers; `hosted_image.spl` consumes library names and
versions. `native_adapter.spl` selects `.tbd` paths but explicitly rejects them.
That refusal remains necessary until a real provider reader/consumer is wired.

Text interfaces do not supply mapped dylib VM addresses. The immediate dependency
is an acyclic typed provider seam that does not require those addresses. Binary
projection must still call the existing validating binary parser before removing
address-only details; it must not weaken binary validation to imitate text stubs.

## Mandatory implementation stages

### 1. Shared typed provider and actual consumer

Introduce acyclic provider types carrying selected target, install name, current
and compatibility versions, supported symbol kinds/weakness and required
metadata. Preserve absent metadata distinctly from known zero wherever the
format does not define a default. A document-level representation later retains
the main interface and inlined libraries. Do not overload binary addresses with
invented values or call unvalidated caller metadata an admitted artifact.

The existing binary hosted entry remains compatible: decode actual provider
images, project validated contracts, and delegate to the same typed hosted
consumer. The consumer must actually drive dependency load commands and symbol
binding ordinals. Tests compare binary-wrapper output with its validated typed
projection and independently inspect the emitted metadata. Deliberately changed
typed contracts must produce corresponding bytes or a specific rejection.
Public value construction is caller-trusted, not a security or manifest seal.

Frozen immediate interfaces: `provider_types.spl` defines `MachOProviderV1`
with target/platform, install name, packed current/compatibility versions,
`Option` minimum_os/sdk, dependencies (command/name/versions), exports
(name/flags/library_ordinal/import_name), `allowable_clients: [text]` and
`parent_umbrella: Option<text>`. No VM address is present.
`macho_validate_provider_v1(provider, target) -> Result<bool, text>` validates
metadata shape without granting authority.

`binary_provider.spl:macho_read_binary_provider_v1(bytes, target)` returns that
provider only after `macho_read_dylib` succeeds. It then checks the bounded
LC_SUB_CLIENT (`0x14`) and LC_SUB_FRAMEWORK (`0x12`) strings and preserves them.
The original binary reader remains intact. Preserve `Some(0)` for a real binary
SDK field even when minimum_os is positive; it is not invented absence. Preserve
resolver flag 16 and unused unsupported export metadata. Existing selected
weak/absolute/reexport import rejection remains at actual binding selection.

`macho_hosted_link_with_providers(objects, archives, providers, request)` is the
typed production consumer; the original byte-provider API decodes and delegates.
Fixup and image construction consume the same typed metadata. For this initial
seam, nonempty clients or a parent umbrella fail explicitly because actual client
binding is not implemented yet. This prevents policy erasure while retaining
the full stage-3 requirement to implement those permissions positively.

### 2. Both format readers

V4 requires tagged YAML `!tapi-tbd`, version 4, target lists, install name,
target-scoped symbol/metadata groups, and document streams. V5 requires JSON
`tapi_tbd_version: 5`, `main_library`, target_info and optional inline libraries.
An omitted V5 group's targets inherits its library targets; it does not mean
every supported platform. Match architecture and platform together: macOS is
not Catalyst and arm64 is not automatically arm64e.

Current/compatibility version defaults are format-defined 1.0. V5 omitted
minimum deployment defaults to zero per its schema. Do not infer an SDK version
or copy the request's deployment value into absent provider metadata. Library
packed versions have their own component limits; do not blindly reuse the
facade's deployment-version parser.

Reuse `std.common.json.parser.json_parse_strict_with_error` for strict decoded
duplicate-key and trailing-token rejection, with explicit preparse byte/depth
limits and document/symbol bounds. That API does not impose resource quotas.
`std.common.encoding.yaml` currently lacks tags; its underlying flow parser
splits commas without quote/nesting awareness and strips double quotes without
full escape decoding. Its any/null result cannot serve as authoritative V4
validation. Repair/add a reusable strict Result/document-stream parser, or a
bounded domain parser with explicit accepted syntax and fail-closed unsupported
syntax. Never normalize away meaningful data through the permissive parser.

Readers must preserve ordinary/weak/TLV and Objective-C categories, metadata
scope, flags, reexports and undefined-interface information. For baseline 64-bit
ObjC, expand class entries into `_OBJC_CLASS_$_` and `_OBJC_METACLASS_$_` names;
EH and ivar prefixes are `_OBJC_EHTYPE_$_` and `_OBJC_IVAR_$_`. Do not turn
unsupported metadata into regular symbols silently.

### 3. Closure and access rules

Resolve target-selected inline interfaces by install name, then explicitly
configured SDK/search inputs for external reexports. Preserve provenance and
reject incompatible duplicate identities, absent target slices and unresolved
required closure. Bound traversal and detect cycles without unbounded recursion.
Keep direct-library ordering deterministic. An umbrella's reexported symbol
normally binds through its direct library ordinal, rather than arbitrarily
adding leaf libraries to the executable's direct dependencies.

Enforce allowable clients using actual output client identity and the relevant
link relationship. Signing identifier is not automatically client identity.
Parent umbrella is semantic metadata, not independent permission or trust.
Multi-document/subframework closure must be tested through actual binding,
including allowed umbrella use and denied direct access. Do not claim full
closure by flattening every library's symbols into one unrestricted namespace.

### 4. Binding and real SDK integration

Implement weak provider/import behavior with correct selection, absent-weak
handling and dyld binding flags; preserve TLV descriptor kind checks. Reexport
aliases, absolute-provider semantics and SDK linker directives such as `$ld$`
need explicit treatment. Unsupported semantics must produce named errors until
implemented, rather than be counted as completed SDK support.

Wire real SDK/library discovery and all provider paths into native planning,
the file adapter and typed hosted engine. Preserve output on failures before
publication and the existing successful replacement contract. Managed runtime
authority remains enforced by its existing owner. Reading a trusted path or
computing a digest is not a new issuer. Full SDK/compiler native execution and
all five host qualifications remain separate mandatory gates.

## Evidence and acceptance plan

Installed WSL Ubuntu tools include `llvm-readtapi` 21.1.8, `llvm-nm` and
`ld64.lld`. `llvm-readtapi -stubify`, `-extract`, `-compare`, and
`--filetype=tbd-v4|tbd-v5` can generate paired interfaces from repository-owned
`provider_x64/a64.dylib` and hosted TLS dylibs. These are independent external
fixture oracles, not Simple execution. Record exact commands, source artifacts
and expected semantic differences; do not copy an unlicensed SDK wholesale.

- Binary projection preserves validated install names/versions/kinds and actual
  emitted load commands/bind ordinals. Bad binary ranges remain rejected.
- Paired V4/V5 fixtures select x64/arm64 symbols independently; macOS/Catalyst
  mismatch, missing target, malformed tags/documents, duplicate fields, numeric
  overflow, truncated syntax and resource bounds fail before publication.
- Explicit/default versions and omitted target scopes match TextAPI results.
  ObjC expansions, TLV and weak distinctions survive to the consumer.
- Inline and external reexport chains bind through the expected direct ordinal;
  cycles, conflicting install identities, missing leaves and target mismatch
  produce deterministic outcomes with bounded work.
- Allowed client/umbrella links and denied direct links exercise actual access
  rules; no signing-name substitution or unconditional bypass.
- Real strong/weak/TLV references validate actual fixup bytes, dependency order
  and negative kind checks. SDK directives must not leak as ordinary exports.
- Real selected `.tbd` paths reach both parsers through native file planning,
  not test-only reader entrypoints. Failure preserves destination sentinels.
- Separately execute real macOS SDK/compiler inputs and native launch after
  runtime admission. Cross-produced bytes cannot certify Darwin or other hosts.

## Primary sources and oracle limits

Sources inspected 2026-10-04:

- [LLVM TextStub.cpp](https://www.llvm.org/docs/doxygen/TextStub_8cpp_source.html):
  tagged V4 schema and target-scoped sections.
- [LLVM TextStubV5.cpp](https://llvm.org/docs/doxygen/TextStubV5_8cpp_source.html):
  JSON main/inline libraries, target inheritance and version defaults.
- [LLVM InterfaceFile.h](https://llvm.org/doxygen/InterfaceFile_8h_source.html):
  client restrictions, parent umbrellas and reexport interfaces.
- [LLVM Symbol.h](https://llvm.org/doxygen/Symbol_8h_source.html):
  separate weak-defined/weak-reference/TLV categories and ObjC name prefixes.
- [LLVM issue 114146](https://github.com/llvm/llvm-project/issues/114146):
  documented historical LLD failure to enforce allowable-client restrictions.

Accordingly, LLD success alone is not the client-access oracle. Use primary
semantic requirements and explicit permission tests alongside parser/metadata
comparison. Keep source review, external fixture construction, SSpec execution,
generated manuals, coverage, memory/performance evidence and full host admission
separate. The typed seam is a completed dependency only when its production path
is implemented and verified; it is never a substitute for stages 2 through 4.
