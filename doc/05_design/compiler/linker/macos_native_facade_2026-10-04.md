# Explicit macOS native linker facade

Design lane 2026-10-04, base `4da06603013a468071da66824a933051a4c10b07`.
Owner `/root/linker_research`; session/branch
`work/item4-macos-native-docs-20261004`; isolated worktree
`C:/dev/simple-item4-stream-got-docs-20261004`. This document is the only owned
path. Runtime owns source, acceptance owns tests, root owns integration and the
five-host matrix; sidecars N/A. Simple execution remains UNRUN.

## Local evidence and integration

`_LinkerWrapper/native_linking.spl` currently sends every explicit Unix internal
request through ELF configuration validation and `internal_link_native`, which
rejects macOS. `link_engine_external.spl` also restricts internal hosted requests
to its implemented ELF/PE targets. Meanwhile `macho/hosted_link.spl` already
constructs actual x64/arm64 two-level PIE executables, eager dyld fixups and
ad-hoc signatures from object/archive/thin-dylib bytes.

The existing hosted implementation requires explicit macOS 11+ minimum/SDK
versions, an entry, signing identifier and image limit. It rejects local TLS,
unwind and unsupported runtime-discovered sections. A facade must preserve
those errors, not promise arbitrary compiler inputs now work.

The selected implementation moves the unchanged `NativeLinkConfig` definition
to acyclic `linker/native_config.spl`; the existing wrapper reexports it for
caller compatibility. New `macho/native_adapter.spl` exports
`MachONativePlanV1`, `native_macho_plan_v1` and
`native_macho_link_files_v1`. Planning consumes the real config. Execution reads
real files, invokes `macho_hosted_link`, and uses the existing image publisher.
It must not import the wrapper, avoiding a wrapper/adapter cycle.

Exact public signatures:
`native_macho_plan_v1(arch: text, config: NativeLinkConfig, output: text)
-> Result<MachONativePlanV1, text>` and
`native_macho_link_files_v1(plan: MachONativePlanV1, object_files: [text],
runtime_archives: [text], output: text) -> Result<text, text>`.
Plan fields are `request: MachOHostedRequest`, `libraries: [text]`,
`library_paths: [text]`, `runtime_path: text`, `runtime_bundle: text`, and
`verbose: bool`. Literal `runtime_path="none"` selects no runtime and rejects
nonempty supplied runtime archives. Empty runtime_path retains existing wrapper
auto-resolution; it must not silently mean no runtime. Other selections require
actual runtime archive inputs at the file-adapter boundary. Passing paths is
not a new authority issuer: production remains responsible for existing runtime
selection/admission before invoking the shared adapter.

The production macOS internal arm uses this exact adapter after existing managed
admission, host matching and runtime-provider validation. Successful receipts
identify `internal:macho`. Existing managed native admission requires its admitted
external linker and continues to refuse internal selection. A direct byte/file
adapter test is not permission to bypass that production gate.

## Configuration contract

All fifteen existing fields require explicit treatment. Unsupported requests
fail before input consumption/publication rather than silently dropping policy.

| Field | Required treatment |
|---|---|
| libraries | Resolve requested archives/thin dylibs, rejecting object files and unsupported provider formats in this list. Positional inputs separately classify objects, archives and thin dylibs. |
| library_paths | Deterministic requested library search; consume the bytes of the actual selected file. |
| runtime_path | Existing provider selection and validation; no guessed runtime directory or synthesized archive authority. |
| runtime_bundle | Preserve the named runtime authority and existing strict archive selection; no default invented bundle. |
| target_triple | Require supported Darwin target and selected architecture; production requires matching host. |
| linker_abi | Validate the macOS ABI spelling consistently with the shared target mapper. |
| pie | Hosted core emits PIE; reject false. |
| debug | Reject true until actual requested debug behavior exists. |
| strip_output | Reject true until actual strip policy exists. |
| prefer_size_linker | Reject true until an implemented equivalent exists. |
| verbose | Diagnostics only; must not alter linked bytes or dispatch. |
| allow_duplicate_definitions | Forward the real value: true retains the first selected strong definition; false rejects duplicate strong definitions. See macho_duplicate_policy_2026-10-04.md. |
| allow_cc_fallback | Explicit internal requests never silently fall back, consistent with the existing internal selection contract. |
| retained_symbols | Reject nonempty until actual root retention is implemented. |
| extra_flags | Parse only the explicitly frozen Mach-O grammar; reject unknown, missing or conflicting options. |

Library search follows configured directory order, trying `.dylib`, `.tbd`,
then `.a` within each directory. A selected `.tbd` fails explicitly; it must not
silently redirect to a later archive. Explicit provider paths bypass name search.

Minimum OS and SDK must come from explicit configuration, never the host version
or guessed SDK path. Signing identity is structural input, not artifact trust.
An image byte cap is a structural allocation limit, not whole-job RSS/no-swap
certification.

The frozen flag grammar requires `-platform_version macos MIN SDK` and
`--macho-signing-identifier ASCII_NAME`. Versions use
`major[.minor[.patch]]`, packed 8:8:8 with bounded components and the core's
macOS 11+ minimum/SDK ordering checks. Optional flags are `-e ENTRY` (literal
default `_main`), repeated `-rpath PATH`, and
`--macho-max-image-bytes DECIMAL` (default `0x7fffffff`). Duplicate singleton
flags, unknown flags, missing values and NUL are errors. The core also rejects
invalid or duplicate rpaths. A default `NativeLinkConfig` therefore cannot
silently select guessed platform/signing inputs; tests supply explicit settings.

## Provider boundary and primary research

`macho/dylib.spl:macho_read_dylib` accepts only thin little-endian 64-bit
MH_DYLIB with matching CPU/subtype, checked load commands, mapped export
addresses and actual trie/symbol metadata. It does not read SDK `.tbd` files,
universal slices, or shared-cache mappings. Do not reinterpret text stubs as
Mach-O bytes or fabricate system exports to make fixtures pass.

[LLVM's TextStub reader](https://llvm.org/doxygen/TextStub_8cpp_source.html)
models target-qualified text interfaces separately from binary images.
[Its V5 reader](https://llvm.org/docs/doxygen/TextStubV5_8cpp_source.html)
also handles JSON interface metadata and reexport libraries. Supporting these
providers requires explicit format/version parsing and accurate target, install
name, symbol-kind and reexport contracts.
[Apple's cache format](https://github.com/apple-oss-distributions/dyld/blob/main/include/mach-o/dyld_cache_format.h)
defines a distinct mapped cache container. A future cache provider needs mapping,
subcache identity and address translation; pathname existence is insufficient.
Primary sources inspected 2026-10-04.

This facade can positively consume supplied thin dylibs and static archives.
That does not close typical SDK/libSystem provider availability, native dyld
execution, compiler bootstrap, or full macOS support.

## Acceptance and publication

Use existing real fixtures under `test/fixtures/linker/macho/`:
`hosted_start_x64.o`, `provider_x64.dylib`, `provider_x64.o`, `provider_x64.a`,
`hosted_start_a64.o`, and `provider_a64.dylib`. Adapter tests on Windows use a
typed explicit target; they do not spoof host environment or claim macOS runs.

Positive tests independently inspect published Mach-O CPU, LC_MAIN,
LC_BUILD_VERSION, dependency names, fixup targets and signature metadata.
Exercise real object/archive selection, explicit library search, rpath/version
propagation and actual destination replacement. Preserve
`native_image_publish` replacement behavior; this is not the streamed no-replace
API. Input/planning/provider failures before publication preserve a sentinel.

Negative matrices exercise all unsupported config fields, unknown flags,
missing platform settings/default config, malformed or mismatched providers,
`.tbd`/cache rejection, actual production host mismatch and retained managed
admission refusal. Default hosted external dispatch must remain unchanged;
`SIMPLE_LINKER=internal` is explicit opt-in.

Native execution on Windows, Linux, SimpleOS, FreeBSD and macOS remains tracked
separately. Cross-produced bytes cannot qualify the target host. Full runtime,
manual generation, branch coverage and performance gates remain open.
