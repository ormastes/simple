# Mach-O TextStub readers and semantic document boundary

Stage-2 frozen implementation design, 2026-10-04; base
`e1495a1e9dd4a8a224e24da2f3e2d21c11652d4d`.
Owner `/root/linker_research`, session/branch
`work/item4-macho-tbd-docs-20261004`, isolated worktree
`C:/dev/simple-item4-stream-got-docs-20261004`. This document is the sole owned
path. Runtime owns reader code, acceptance owns tests, root integrates; sidecars
N/A. No new runtime admission was established; execution remains UNRUN.

This supplements `macho_sdk_providers_2026-10-04.md`. Both V4 YAML and V5 JSON,
then closure/access/binding and real native SDK execution, remain required.
Reader success does not complete the four-stage SDK plan.

## Shared document contract

Use an acyclic TextStub IR rather than constructing fake binary providers.
Frozen public names:

- `MachOTbdLimitsV1`: maximum input bytes, nesting depth, lexical tokens,
  libraries, source symbol entries and bytes per name.
- `MachOTbdTargetV1`: architecture and platform, preserving exact target identity.
- `MachOTbdSymbolV1`: name, encoding kind (global/ObjC class/EH/ivar), role
  (export/reexport/undefined), weak-definition/reference and thread-local flags,
  and text/data/unspecified segment classification.
- `MachOTbdLibraryV1`: install name, current/compatibility versions, optional
  minimum deployment, flags, Swift ABI, clients, parent umbrella, rpaths,
  reexported libraries and symbols. Retain target availability for inline
  libraries that do not provide the requested slice.
- `MachOTbdDocumentV1`: format version, selected target, main library and inline
  library collection.
- `macho_read_tbd_v1(bytes, target, limits) -> Result<MachOTbdDocumentV1, text>`.

Joint freeze refinement: target is `{arch: RelocArch, platform: i64}`. Retain
`install_names: [MachOTbdInstallNameV1]`, each with `{targets: [text], name: text}`,
and selected `install_name: Option<text>`. Unavailable inline target selection
uses `None`; do not invent a name from the first scoped identity. Main requires a
selected identity. Library `declared_targets` and `selected` preserve availability.
Limits default to max_bytes=16777216, max_tokens=1048576, max_depth=64,
max_libraries=4096, max_symbols=1048576 and max_name_bytes=4096. Callers may lower
these limits; defaults also cap accepted limit settings.

`macho_tbd_main_provider_v1(document, target) -> Result<MachOProviderV1, text>`
performs explicit leaf lowering. Root's native file adapter routes actual selected
`.tbd` bytes through read/lower into the same hosted provider consumer; binary
providers retain real binary validation. Runtime inputs remain archive-only.
Leaf exports preserve ordinary/weak/TLV flags, with selected unsupported weak
semantics still rejected by the hosted consumer. Closure, undefined-interface,
unimplemented flags/clients/umbrella/rpaths/nonzero Swift/directive semantics must
reject explicitly when lowering cannot honor them. This is an implemented leaf
route prerequisite, not a claim the retained full SDK requirements are complete.
The one accepted provider flag is `not_app_extension_safe`: current image
construction leaves `MH_APP_EXTENSION_SAFE` clear, so accepting this metadata
does not assert extension safety. Other flags remain explicit lowering errors.

Schema parsing precedes target selection. Reject malformed groups even if they
would not be selected. Main target absence is a named error. An unrelated inline
library may lack the chosen target without invalidating the main interface;
preserve that distinction for closure diagnostics. Do not replace a missing
target with an empty provider or merge macOS with Catalyst/arm64 with arm64e.

Reexport names remain semantic graph edges. Do not invent ordinal 1, flatten
restrictions, or convert them to regular exports in the reader. Leaf lowering
expands ObjC classes into class/metaclass ABI names, EH entries into EH ABI names,
and ivars into ivar ABI names. EH alone does not imply class exports. Identical
expanded names with identical flags coalesce; conflicting flags reject. Export
name expansion does not implement Objective-C runtime loading or closure.

## Exact format obligations

V4: tagged YAML `!tapi-tbd`, `tbd-version: 4`, required targets/install-name,
current/compatibility versions, flags/Swift ABI, target-scoped exports,
re-exports, undefineds, reexported libraries, clients and parent umbrellas.
Support the actual TAPI document stream and flow lists, including quoted names
and comments without destructive splitting.

V5: numeric `tapi_tbd_version: 5`, main_library, target_info and inline libraries.
Target-info minimum deployment defaults to zero when omitted. Group target lists
inherit library targets when absent. Preserve target-scoped metadata and separate
text/data global, weak and thread_local groups and ObjC categories.

Current/compatibility version defaults are 1.0. Library packed versions use
16:8:8 limits; do not reuse a deployment parser with an 8-bit major limit.
V4 absent minimum stays absent; V5 default-zero minimum follows its schema.
Neither format supplies an invented SDK version or mapped VM address.
Unknown meaningful fields/flags, conflicting singleton metadata and malformed
values must fail explicitly until modeled. Never report full support by dropping
unsupported policy fields. Legitimate format defaults must remain distinguishable
from missing required data.

## Reusable JSON API and strict YAML boundary

At the recorded base `std.common.json.parser.json_parse_strict_with_error`
returns `(any, text)`, rejecting duplicate decoded object names and trailing
tokens. Nodes are tagged tuples: object/Dict, array/list, string/text,
number/f64, boolean/bool, null/nil. `json_object_get` and `json_array_get`
return `any?`. Check node tags before extraction; do not collapse wrong type,
missing property and explicit null into one default. Versions encoded as strings
need exact component parsing; format version must be an exact numeric integer.

The recursive JSON parser lacks resource bounds. Before invoking it, a
quote/escape-aware scan must enforce input/depth/token bounds. Apply collection,
symbol and name limits during semantic construction, before large additions.
Resource-limit failures are parser outcomes, not hard RSS admission.

Current common YAML parsing cannot be used unchanged: flow splitting ignores
quoted delimiters/nesting, tags/document streams lack a strict error contract,
and double-quoted escape decoding is incomplete. A bounded domain reader may
reject unsupported YAML features explicitly, but must cover both actual fixture
syntax and SDK-required syntax before claiming SDK completion. Anchors, aliases,
merge keys and unsupported scalar forms must never be silently normalized.

The implemented YAML profile accepts tagged document streams, block mappings
and sequences, quoted/plain scalar values, comments and multiline flow lists
of scalars. It rejects nested flow collections, multiline quoted scalars, tabs,
graph aliases/anchors, merge keys and block scalar forms. Source and decoded
names are ASCII-only. These explicit restrictions still require validation
against representative real SDKs; fixture acceptance is not general YAML or
complete SDK compatibility. Strict decoded JSON-key rejection intentionally
exceeds LLVM21's observed acceptance of identical duplicate keys.

Resource accounting bounds lexical tokens and source symbol records, including
unselected targets. It does not bound whole-process RSS. ObjC class expansion
may produce two output names per source entry. Name decoding must reject an
oversized decoded value during construction; multiline flow accumulation must
join fragments once rather than repeatedly copying an increasing prefix.

## Acceptance traceability

All cases trace to ITEM4-REQ-006 and the full SDK provider plan. Shared exact
test helper names/API are frozen by root before implementation.

| Obligation | Real oracle and assertion |
|---|---|
| Both readers | Stubify repository-owned x64/arm64/TLV dylibs into V4 and V5 with installed llvm-readtapi21.1.8; decode both into equivalent selected metadata. |
| Independent target selection | Use distinct symbols/versions/restrictions per target; compare extract/compare results and assert exact chosen values, including unavailable main and inline targets. |
| Metadata fidelity | Assert defaults versus absence, 16:8:8 boundaries, flags, Swift ABI, ObjC categories, weak/TLV, clients, umbrella and rpaths. |
| Document closure inputs | Preserve main plus multiple inline install names and reexport edges without fabricated binding ordinals; malformed duplicate identities fail explicitly. |
| Strict syntax/schema | Actual files with malformed/truncated tagged YAML/JSON, duplicate decoded keys, quoting/escape cases, unknown fields, wrong node types and invalid versions yield named errors. |
| Bounded work | Byte/token/depth/library/source-symbol/name limits reject before dependent allocation/recursion; never claim these prove RSS. |
| Production leaf wiring | Actual selected .tbd files flow through native adapter, reader, leaf lowering and hosted bindings; malformed selected files preserve the destination without fallback. Full semantic closure remains required separately. |

External LLVM construction/inspection is separate from Simple SSpec execution.
Do not accept LLVM link success alone as proof of allowable-client policy:
historical LLD ignored such restrictions. Use primary policy rules and real
allowed/denied link cases in the later closure stage.

## Sources and remaining gates

Primary schema sources inspected in this research lane:
[V4 TextStub.cpp](https://www.llvm.org/docs/doxygen/TextStub_8cpp_source.html),
[V5 TextStubV5.cpp](https://llvm.org/docs/doxygen/TextStubV5_8cpp_source.html),
[InterfaceFile metadata](https://llvm.org/doxygen/InterfaceFile_8h_source.html),
[symbol categories](https://llvm.org/doxygen/Symbol_8h_source.html), and
[client-policy oracle limitation](https://github.com/llvm/llvm-project/issues/114146).

Still required: actual reexport/alias closure, client and umbrella enforcement,
weak/TLV binding semantics, SDK directive handling/discovery, native application
execution and all five host qualifications. Managed authority remains intact;
Simple's linker remains opt-in. No parser or typed metadata value is a trust seal.
