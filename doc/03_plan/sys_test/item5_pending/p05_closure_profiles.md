# Item 5 exact closure and profiles acceptance criteria

Status: NOT_IMPLEMENTED. These are acceptance criteria for intentional failing SSpec scaffolds, not implementation or execution evidence.

Canonical requirements: [selected requirements](../../../02_requirements/feature/runtime_optional_provider_binary_size_optimization.md).

Each criterion must eventually use real build, loader or measurement observations. Missing runners, fixtures, admitted baselines or evidence remain incomplete. No test has been run for this scaffold.

## I5-P05-AC01: retain only the demanded entry closure

- Requirements: REQ-003.
- Status: NOT_IMPLEMENTED.
- Setup: Build a no-import entry and an entry demanding one capability from the same frozen source and target; record the complete input graph, command arguments and unused optional providers, compiler backends and tools.
- Action: Resolve and link each exact entry closure, then start each artifact with loader tracing.
- Observable acceptance: Every retained dependency is reachable from that entry or an explicitly justified runtime root; unused arguments do not retain dependencies, and unrelated libraries, providers, backends and tools are absent from link and startup inventories.

## I5-P05-AC02: exclude collector code from allocation-free NoGC output

- Requirements: REQ-007 REQ-013.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare an allocation-free NoGC hello with a checked allocation/effect closure and a target collector symbol and constructor inventory.
- Action: Build, inspect its map and sections, and execute with initialization tracing.
- Observable acceptance: No collector module, symbol, section, dynamic dependency or initialization appears; the receipt identifies the NoGC proof and enumerates all remaining runtime roots.

## I5-P05-AC03: omit exception facilities only with complete release-small proof

- Requirements: REQ-008.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a release-small entry whose complete closure proves exceptions, cleanup unwinding and RTTI unnecessary, with target-specific inventories for each facility.
- Action: Produce the proof, link the artifact and inspect sections, symbols and dependency records.
- Observable acceptance: Exceptions, unwind tables, RTTI and their libraries are absent, and the artifact is bound to the exact closure proof authorizing each omission.

## I5-P05-AC04: refuse unproved release-small omissions

- Requirements: REQ-008 REQ-011.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare entries with required unwinding, required RTTI and an unknown dependency effect; record their expected semantics and failure paths.
- Action: Request release-small with each incomplete or contradictory omission proof.
- Observable acceptance: No artifact claiming unsupported omissions is admitted; the tool either gives a specific refusal or retains the required facilities through an explicitly recorded ordinary-release choice, preserving demanded semantics.

## I5-P05-AC05: isolate demanded foreign exception facilities from the base executable

- Requirements: REQ-009 REQ-013.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare one immutable base executable and a separately packaged foreign provider requiring exceptions, unwinding or RTTI; capture its isolated dependency inventory.
- Action: Compare the base with and without provider installation, then demand the foreign capability and exercise its exception path.
- Observable acceptance: Provider installation does not enlarge or change the base executable; exception facilities occur only in the demand-loaded provider closure, and the requested operation and error path complete with reasoned dependency receipts.

## I5-P05-AC06: preserve required diagnostics in ordinary profiles

- Requirements: REQ-010 REQ-011.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a diagnostic-producing program with expected debug and ordinary-release behavior and a separately named release-small configuration.
- Action: Build and run all three profile selections, including the program's failure path.
- Observable acceptance: Debug and ordinary release retain their required diagnostics; release-small is recorded as a separate profile and cannot globally disable language features or alter the other profiles.

## I5-P05-AC07: retain demanded language features across supported architectures

- Requirements: REQ-011.
- Status: NOT_IMPLEMENTED.
- Setup: Enumerate every supported native architecture and demanded language feature from the admitted support matrix, with executable success and failure fixtures.
- Action: Build and execute each supported architecture-feature combination using its admitted host or target runner.
- Observable acceptance: Every supported combination preserves its specified results and errors; missing runners, missing features or omitted matrix cells remain incomplete rather than being counted as successful.

## I5-P05-AC08: account for every retained root with a reason

- Requirements: REQ-013.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare an entry with module, section, provider, dynamic-library, constructor, export and metadata roots, plus independently collected linker and loader inventories.
- Action: Build and demand its providers, then join closure and loader receipts against the observed inventories.
- Observable acceptance: Every retained item in all seven root categories has a concrete reachability or ABI reason and identity; no retained item is unexplained and receipts do not claim nonexistent roots.

## I5-P05-AC09: remove unreachable constructors while preserving required initialization

- Requirements: REQ-003 REQ-013.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a demanded module with an observable required constructor and an unrelated optional module with a distinct constructor effect.
- Action: Link only the demanded entry and execute it while recording constructor calls and root reasons.
- Observable acceptance: The required constructor remains, is justified and executes as specified; the unrelated constructor and its dependency closure are absent and its effect never occurs.

## I5-P05-AC10: preserve demanded exports and metadata without retaining unrelated features

- Requirements: REQ-003 REQ-011 REQ-013.
- Status: NOT_IMPLEMENTED.
- Setup: Prepare a provider capability with required exported entry and metadata roots plus unrelated exported implementation fixtures outside the demanded closure.
- Action: Build with exact closure, resolve the demanded export and metadata through the real loader, then invoke the capability.
- Observable acceptance: Demanded exports and metadata remain usable with explicit root reasons; unrelated implementations do not enter the base closure merely because they exist, and the demanded capability retains its specified behavior.
