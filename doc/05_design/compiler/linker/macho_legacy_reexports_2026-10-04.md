# Mach-O legacy reexport command integration

2026-10-04; inspection base `487d64cfac314787e89c8bb7304e0a24eae3d450`.
Owner `/root/linker_research`, isolated branch
`work/item4-macho-legacy-reexports-docs-20261004`; sidecars N/A.
Runtime owns provider projection/closure, acceptance owns fixtures/spec/manual,
root owns integration and final verification. Simple execution remains UNRUN.

## Requirement and current gap

The retained full SDK and five-host linker requirements include legacy provider
visibility semantics. At the inspection base, `provider_closure_source.spl`
explicitly refuses commands `LC_SUB_UMBRELLA` and `LC_SUB_LIBRARY`; merely
removing that refusal would silently hide imported definitions. Existing native
composition already routes real provider files through the same closure, so
implementing checked projection and actual graph edges closes a production gap.
No new CLI flag, synthesized provider, or signing identity is needed.

This change does not complete SDK directives, weak imports, native Darwin
qualification, managed internal-engine admission or the other host execution
gates. External linker selection remains the default.

## Primary evidence and selected compatibility profile

Apple's format header describes legacy selectors as making dependency exports
visible through the parent library. Its example normalizes
`libobjc_profile.A.dylib` to `libobjc`. It separately describes subframework
client restrictions and the no-reexports optimization bit.
[Apple loader.h](https://raw.githubusercontent.com/apple-oss-distributions/xnu/main/EXTERNAL_HEADERS/mach-o/loader.h).

Current ld64's binary parser matches umbrella selectors against a path's final
component, requiring a slash. Library matching accepts a slashless name, removes
the first dot suffix, and uses a prefix comparison; it does not implement the
header example's underscore normalization. The loop marks every match and does
nothing for unmatched selectors. Compressed-linkedit parsing filters ordinary
dependencies before historical inference.
[Apple macho_dylib_file.cpp](https://raw.githubusercontent.com/apple-oss-distributions/ld64/main/src/ld/parsers/macho_dylib_file.cpp).

The generic ld64 owner skips historical discovery under the no-reexports flag.
Without a modern explicit reexport command, it can inspect ordinary children's
parent-umbrella metadata and compare that name with the requesting physical
file's basename. That inference is distinct from direct client permission.
[Apple generic_dylib_file.cpp](https://raw.githubusercontent.com/apple-oss-distributions/ld64/main/src/ld/parsers/generic_dylib_file.cpp).

The selected project profile uses exact header-derived library stems before the
first dot or underscore, exact umbrella leaf matching, all matches and unmatched
no-ops. It intentionally does not reproduce ld64's observed prefix quirk. Explicit
selectors operate even in compressed providers. There is no blanket ld64/LLD
equivalence claim; fixture construction tools alone cannot establish this policy.

## Frozen semantic contract

- `LC_SUB_UMBRELLA` is `0x13`; `LC_SUB_LIBRARY` is `0x15`. Preserve their ordered
  names after checked decoding within the original validated command envelope.
  Require at least 16 command bytes, offset at least 12 and below command size,
  a terminator inside that command, nonempty ASCII name and existing name limits.
- Preserve dependency order and original commands. A selector identifies
  existing `LC_LOAD_DYLIB` (`0x0c`) or `LC_LOAD_WEAK_DYLIB` (`0x80000018`)
  records; it never invents a dependency path. Lazy and upward records retain
  their existing behavior and are not new legacy candidates.
  Umbrella selection compares the final component only when a slash exists.
  Library selection compares the entire canonical stem, retaining the `lib`
  prefix and stopping at the first `.` or `_`; slashless libraries are permitted.
- Every matching dependency becomes a whole-library reexport edge. Duplicate
  selectors do not multiply edges. Multiple matching version/profile paths are
  not a selector ambiguity error. Existing conflicting provider identities and
  physical-context checks still apply when resolving those paths.
- An unmatched selector is a no-op. A matched dependency whose file is absent,
  malformed, incompatible or wrongly identified returns the existing named
  error before publication. Do not mistake an unmatched selector for a request
  to probe a guessed library filename.
- `MH_NO_REEXPORTED_DYLIBS` (`0x100000`) suppresses explicit legacy and inferred
  whole-library edges. Continue validating command strings. Existing modern
  `LC_REEXPORT_DYLIB` and per-symbol alias behavior remains unchanged.
- Implicit subframework discovery is enabled only for genuine old binary
  provenance: no `LC_DYLD_INFO` (`0x22`), `LC_DYLD_INFO_ONLY` (`0x80000022`) or
  `LC_DYLD_EXPORTS_TRIE` (`0x80000033`), no no-reexports flag, and no
  `LC_REEXPORT_DYLIB` (`0x8000001f`). Text stubs and existing constructed providers
  default to no such inference.
- Eligible inference loads ordinary children through the existing contextual
  resolver and compares a child's `parent_umbrella` to the requesting provider's
  physical source basename, requiring a slash. Only matching children acquire
  whole-library edges. Do not substitute install name, output name, signing
  identifier or executable client name. Modern unselected ordinary dependencies
  remain unprobed.
- Preserve direct-root access checks and existing indirect access behavior.
  Discovery of a subframework does not authorize a forbidden direct link.
  Outward bindings retain original import names and direct root ordinals.

## Shared ownership and integration

`MachOProviderV1` gains `sub_umbrellas: [text] = []`,
`sub_libraries: [text] = []`, `no_reexported_dylibs: bool = false` and
`infer_subframeworks: bool = false`. Binary projection runs the existing full dylib
reader before decoding extra commands. The source owner removes its blanket
legacy refusal only when that projection and the closure consumer exist.

The closure builds selector membership once, accounts for that work and examines
each dependency in original order. Existing whole-reexport and alias conditions
are combined with legacy selection without duplicating an ordinal edge. Inferred
probes also consume existing source, byte, symbol, depth and work quotas.
Inspect an unmatched child's retained parent metadata without activating/lowering
it: unrelated deployment versions or unsupported export policy must not poison
the link. Structural source validation and its resource charges still apply.
Existing
contextual runpaths, inline-catalog priority and physical identity conflict rules
apply unchanged. No recursive all-dependency crawl of modern SDK libraries is
introduced by the old-format compatibility path.

No public entrypoint needs replacement. The actual native adapter continues
through the existing V2 closure. Pure metadata is caller-trusted, not authenticated
plugin authority. Logical quotas are not RSS/no-swap or worker certification.

## Acceptance obligations

All authored scenarios trace ITEM4-REQ-006 and use canonical `std.spec.step`;
test helpers use `item4_macho_legacy_`. Guard actual mutation targets before access.

1. Real ordinary-dependency binary roots on both CPUs hide leaf symbols without
   selectors and expose them with each legacy command. Inspect actual outward
   binding names/root ordinals and direct load commands independently.
2. Exact umbrella leaf and library dot/underscore stem boundaries, including
   slashless library names and names that only share a prefix. Multiple matching
   dependencies provide distinguishable exports; unmatched and duplicate selectors
   neither invent paths nor duplicate edges.
3. Matched missing, malformed, wrong-target/identity and incompatible providers
   preserve an existing output sentinel. Unmatched unavailable dependencies do
   not become mandatory merely because a selector command is present.
4. Actual old-format symtab-backed providers exercise matching and mismatching
   child `LC_SUB_FRAMEWORK`, physical filename versus install-name distinction,
   and direct client refusal. Modern ordinary-dependency controls stay hidden.
5. Header no-reexports suppresses legacy/inferred edges while malformed selector
   strings still reject. Modern reexport/alias paths preserve prior behavior.
6. Checked size, offset, empty name and missing terminator mutations use successful
   original-reader baselines. Actual multi-edge/cyclic graphs terminate under
   the retained query policy; lowered work/source budgets fail honestly.

External fixture inspection, source review, authored tests and executed Simple
acceptance are separate evidence. Native host/compiler corpus, manuals generated
from execution, coverage and representative latency/RSS remain open.

## Exact candidate source review

Independent review found no concrete P0/P1 in four-file core `89da96988ee`,
hosted API guard `c6dcb1f96bb` with classic-leaf refinement `f77ad587503`, main
acceptance through `006e145c405`/manual `7052901d52d`, and modes acceptance/manual
`9a4e14a9eb4`. Initial intent preceded production; later review-driven coverage
was added after implementation, without claiming observed RED/GREEN. The guard requires a
closure for unsuppressed selector metadata or inferred visibility with at least
one ordinary/weak dependency; provenance alone does not refuse a classic leaf.

Nine main authored scenarios cover real both-CPU selectors, hidden/suppressed
dependencies, classic physical-parent inference and modern controls, command
string mutations, exact dot/underscore stems with shorter/longer mismatches,
dormant no-closure compatibility, and inactive high-deployment children.
The inactive-child case uses a root's real symbol-table exports and a validated macOS99
child whose nonmatching umbrella must not activate deployment checks.
The all-match case uses two real dependency identities: an empty first provider
and a later provider supplying the required imports, retaining outward root1.

Three separately authored modes scenarios add ordinary-to-weak/lazy/upward
command mutations with a present provider, matched missing-file failure with
destination preservation, and unmatched absent dependency success through a
modern root's own exports. The weak case verifies command-class visibility only;
absent weak dependencies and weak-import binding semantics remain open.

Dedicated quota and additional alias-interaction boundaries in the broader
matrix remain acceptance obligations. The fixture recipe records original LLVM
construction and subsequent bounded mutations; signatures were not regenerated.
All Simple/native execution remains UNRUN and no SDK/host row is complete.
