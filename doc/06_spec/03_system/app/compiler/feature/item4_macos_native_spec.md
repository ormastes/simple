# Explicit internal Mach-O native file adapter

Six authored scenarios, **UNRUN**, in
`test/03_system/app/compiler/feature/item4_macos_native_spec.spl`.
This manual is authored, not generated execution evidence.

| Requirement | Scenario and oracle |
|---|---|
| ITEM4-REQ-006 | Actual x64 and ARM64 objects plus dylibs yield MH_EXECUTE/PIE images with CPU, entry, minimum/SDK, dependency install name, eager bind stream, local rebase pointer and bounded embedded-signature header checks. |
| ITEM4-REQ-006 | Actual x64 object and archive providers resolve the expected call displacement and local GOT target; successful publication replaces an existing sentinel according to the established publisher contract. |
| ITEM4-REQ-006 | Malformed/duplicate/unknown flags, unsupported policy fields, invalid CPU and invalid output reject in the pure planning API before file reads. |
| ITEM4-REQ-007 | Missing, malformed, incompatible and unresolved inputs preserve existing output bytes. |
| ITEM4-REQ-006 | Default configuration refuses unsupported implicit policy rather than silently selecting options. |
| ITEM4-REQ-006 | A bare library name resolves an actual task-owned dylib through configured library_paths, with explicit image-byte limit checked. |

The named-search case then places a real stub file before a valid archive in the
same directory. Selecting `.tbd` must fail and preserve a destination sentinel;
removing only that stub makes the unchanged plan select the archive and produce
independently checked relocated bytes. This is refusal coverage, not SDK-stub
parsing support or fallback permission.

The tests use checked-in assembler/linker-produced fixtures in
`test/fixtures/linker/macho`; reproduction is documented by that directory's
`RECIPE.md`. Temporary output directories are unique and owned by each case.
Positive requests explicitly supply platform, SDK and signing identifier, with
PIE enabled and unsupported duplicates/debug/strip/retained policy disabled.
Dylib coverage uses both positional inputs and configured library paths, with
an explicit emitted LC_RPATH. Runtime-none/nonempty-archives and unresolved
runtime archive ownership reject before publication; error tokens identify the
intended failing contract rather than accepting arbitrary failures.

Future command after independent runtime admission:
`<runtime> test test/03_system/app/compiler/feature/item4_macos_native_spec.spl`

These are real same-process file-adapter and byte-construction assertions.
No successful Darwin launch, executable permission check, full native-build
receipt routing, managed-runtime admission, bounded RSS, or five-host run is
claimed. The retained managed gate must remain intact; its host/runtime evidence
is a separate integration obligation. Publisher replacement is intentional;
only validation/construction failure promises destination preservation here.
