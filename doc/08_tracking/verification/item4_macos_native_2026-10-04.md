# macOS native facade verification

STATUS: FAIL — full item4/Phase 4 and five-host execution remain incomplete.

The explicit internal Unix route currently enters ELF handling even on macOS.
This lane connects the existing Mach-O image builder to native file/configuration
and request dispatch without changing hosted defaults or managed admission.
Acceptance must use actual object/archive/dylib fixtures and independently inspect
published commands and bytes, including failure preservation of a real sentinel.

The adapter is a prerequisite, not complete SDK support: text-based dylib stubs,
dyld-cache providers, remaining TLS/unwind/provider semantics, trusted internal
managed admission and actual x64/arm64 Darwin execution remain separate gates.
Windows/Linux/SimpleOS/FreeBSD native completion also remains open.

Simple compilation, executable acceptance, docgen, coverage, compiler/lib/MCP
and native performance qualification remain UNRUN without an admitted deployed
self-hosted runtime. Source and structural evidence must be recorded separately.

Source outcome: `784e0eb60cb` implements the typed planner, actual file adapter,
native wrapper and request dispatch, with the unchanged native configuration
type/default reexported from its acyclic module. Independent source review found
no P0/P1 after correcting positional dylib handling and unresolved-import outcome
classification. Initial test intent `5d89d9b4e6c` preceded implementation.

Portable acceptance covers actual images and failure-preserved destinations.
The explicit host probe is
`test/02_integration/compiler/linker/macos_native_host_acceptance.spl`; it is not
part of automatic portable spec discovery, requires real Darwin plus externally
selected internal linking, and fails unmet prerequisites. It checks the wrapper
receipt, actual output bytes and executable permission, not loader execution.
An end-to-end typed request InputError regression and actual Darwin launch/signing
remain open. No host gate is discharged by a source-authored assertion.

Current runtime check: both the primary workspace and integration workspace lack
their `bin/release` directory. No unadmitted producer or Rust seed was substituted.

Final source/manual review binds core `784e0eb60cb` and acceptance through
`e5cd4ac2b90`: no P0/P1 findings. Six portable scenarios cover named lookup,
selected `.tbd` refusal without archive fallback, runtime consistency, actual
provider forms and independent image oracles. The additional Darwin probe remains
explicitly invoked and UNRUN.

Integration rebased onto `416a653d887e04f04028d7fee6d13e74973476f9`.
An interrupted rebase left an unowned index lock and its intended documentation
patch; after verifying no live owner, recovery completed the remaining sequence.
Final range-diff showed all 17 reviewed patches equal. Whitespace, direct-env
working/staged guards, numbered-artifact classification and manual layout passed.
The committed test-tree delta passed: 3151 inherited offenders, zero introduced.
Evidence list: `C:/dev/simple/.git/item4-macos-native-preexisting-offenders.txt`.
These structural results do not change the full verification FAIL/UNRUN status.
