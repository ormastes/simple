# Item 4 linker acceptance and TDD plan

Date: 2026-10-03. Target: `release/1.0` at
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a`.
Status: specification in progress; execution and certification unverified.

Full coding continuation: RV64 static ELF image linking, freestanding Mach-O
construction, FreeBSD hosted startup/identity, explicit static file publication,
checked spill transactions, retained ELF record reading and section emission
have source implementations and executable specs. These supersede earlier
statements that only relocation helpers or budget arithmetic exist. The source
review report records exact evidence. No new runtime PASS is claimed.
Full bounded linking, hosted dyld composition/signing, RISC-V dynamic/TLS,
dynamic-pack lifecycle binding, and full-product/performance execution remain
unfinished acceptance work. This is not a reduction of ITEM4-REQ-001..010.

Implementation update, 2026-10-03: after the tests were committed, the user
instructed `fix what you can`. The hosted ELF engine now rejects selected
non-ET_REL archive members before resolution/layout and rejects embedded NUL
in a dynamic interpreter path before input processing. The existing regression
scenarios cover both changes; the interpreter scenario pins the exact error.
This is test-first authorship followed by source-reviewed implementation, not
an observed RED/GREEN cycle. Runtime execution and all broader gates remain open.

## Implementation continuation

The user's `go impl` instruction continues source implementation. Added owners
and executable regression coverage are now:

| Implemented source behavior | Executable regression authority | Evidence status |
|---|---|---|
| ELF section-header table and file-backed payload bounds use subtraction before reads, preserving NOBITS/NULL semantics | `item4_linker_input_bounds_spec.spl`: four scenarios, including overflow-sized offsets/sizes and unchanged NOBITS output | Source reviewed; SSpec unexecuted |
| Section-backed DSO dynamic tables require DT_NULL, matching the sectionless path | `item4_linker_dynamic_acceptance_spec.spl`: original DSO succeeds; mutation removes every dynamic terminator and must fail through reader and linker | Source reviewed; SSpec unexecuted |
| DSO symbol/version/dependency strings must terminate within their declared string table | Same dynamic spec: mutate the final SONAME terminator while preserving all bounds | Source reviewed; SSpec unexecuted |
| Native-link success carries actual engine identity through external/internal/driver/SMF routes; legacy output APIs project the same result | `item4_linker_engine_receipt_spec.spl`: result/error projections, exact path identity, and real direct-failure then C-driver fallback control | Source reviewed; Linux integration unexecuted |

The DSO filename `libadd_x64.so.1` contains SONAME `libadd_x64.so`. Acceptance
expectations now use the embedded value, established from fixture bytes. The
earlier filename-based expectation was a test-oracle error, not product RED.

`NativeLinkSuccessV1 { output, engine_id }` and `link_to_native_with_engine`
carry execution identity without re-probing the host after success. `cc` names
the C-driver route, not its downstream linker. Unknown executable paths remain
their own identities. Accounting remains NotCertified; result threading alone
does not certify memory or platform behavior. The request adapter consumes the
typed result, but a forced-fallback LinkRequest integration scenario remains
open because its current schema cannot express the driver-only extra flags.

The diagnostic probe `test/fixtures/linker/diagnostic/item4_linker_probe.spl`
uses production calls and nonzero exit codes for the NUL interpreter and ELF
table-overflow checks. It is separate from modern SSpec. An unadmitted pure-Simple
Stage 2 candidate can compile it only as bounded diagnostic work; its command,
candidate/source hashes, outputs and process receipts live in the session-owned
`build/item4-diagnostic/`. No diagnostic outcome substitutes for admitted SSpec,
core/MCP checks, generated manuals or release qualification.

The bounded candidate `--help` succeeded. Three diagnostic build attempts then
established source-family admission, required first-build inventory initialization,
and a 120-second cold-init timeout. No probe executable or behavioral result was
produced. The wrapper reaped the timed-out process and caches were preserved.
See `doc/08_tracking/bug/item4_source_inventory_cold_init_timeout_2026-10-03.md`;
no fourth attempt is authorized by this iteration's bounded verification plan.

This is an executable acceptance breakdown of the existing seven-item plan's
item 4 and the linker research G0-G6 gates. It does not replace the full linker
scope with the first portable test slice. Existing decisions remain selected;
new scope or exclusions require user selection.

## Requirements and decisive evidence

| ID | Existing requirement | Concrete acceptance and evidence |
|---|---|---|
| ITEM4-REQ-001 | Retained MDSOC++ owners and interfaces | Map each retained layer to its current public owner and callers; closure checks prove no new sibling-private imports; stale proposed/dead-owner claims are dated and superseded. |
| ITEM4-REQ-002 | Actual engine and honest failure | Route an explicit internal request through the production facade; assert internal engine receipt and executable result. Force external-provider failure followed by an allowed compiler-driver fallback; receipt must identify the engine that actually succeeded. Unsupported format/budget must return a named failure before publishing output. |
| ITEM4-REQ-003 | Symbols, archive fixpoint and dead stripping | Link direct and archive-provided definitions, including a second-pass dependency; assert resolved image and deterministic extraction. Reject missing and duplicate strong symbols. Keep weak/common semantics and GC roots; dead-only undefined references do not poison live output. Selected archive members must be ET_REL. |
| ITEM4-REQ-004 | Relocations and diagnostics | For each admitted machine, compare relocation bytes to independently specified values; reject overflow, unsupported types, invalid symbol indices and patches crossing section boundaries before publication. |
| ITEM4-REQ-005 | Dynamic dependencies, TLS, unwind and stripping | Link the real dynamic corpus; inspect DT_NEEDED/SONAME, hash policy, visibility and symbol versions; execute TLS/unwind behavior. Strip nonallocated symbol tables without changing executable behavior or required dynamic symbols. |
| ITEM4-REQ-006 | Explicit format and host admission | ELF x86_64/aarch64 and PE AMD64/ARM64 each need byte checks plus native execution. Mach-O and FreeBSD remain open gates until implemented and run, or explicitly excluded by the user. SimpleOS needs the retained firmware/board ladder. An ELF result never establishes PE/Mach-O support. |
| ITEM4-REQ-007 | Deterministic output and actionable errors | Repeat identical requests and compare all output bytes. Missing/duplicate/type/machine/relocation failures identify the offending symbol, object or archive member. A failed link must leave no newly published image. |
| ITEM4-REQ-008 | Complete compiler and representative applications | Build, internally link and execute the pinned full compiler and representative application corpus on each claimed target; preserve commands, input identities, output hashes and exit/output assertions. Tiny fixtures do not satisfy this row. |
| ITEM4-REQ-009 | Performance and bounded memory | Paired cold/warm runs against pinned mold/lld record link time, whole-job peak memory and output size. Investigate 2% regressions. Bounded full-product links must remain below 6,000,000,000 bytes under QualifiedJobScope and match fast output digests; MeasuredOnly is not certification. |
| ITEM4-REQ-010 | Existing G5 linker lifecycle and recovery | Add/replace linker aspects without kernel edits; old-generation sessions remain valid; static recovery link does not depend circularly on the failed dynamic provider. This is the original linker G5 gate, not an expansion into item 5. |

## First modern SSpec slice

Executable authority:
`test/03_system/app/compiler/feature/item4_linker_acceptance_spec.spl`.
Use `std.spec.*`, canonical `std.spec.step`, real production imports, and built-in
matchers. Helpers are `item4_load_elf_fixture`, `item4_static_link_error`, and
`item4_archive_with_member_type`; they must fail on missing fixtures/members.
No helper may manufacture a successful linker result. Every scenario carries
its requirement ID and explicit setup/action/check steps.

| Scenario | Input/action | Required result | Evidence level |
|---|---|---|---|
| ELF x86_64 image | Link checked-in start/provider ET_REL fixtures through `elf_static_link`; parse emitted bytes and independent program-header fields | ET_EXEC, correct machine, bounded/aligned PT_LOAD ranges, no writable-executable load, entry covered by executable file bytes; identical repeat output | Image and segment assertions authored; not executed |
| ELF aarch64 image | Same using aarch64 fixtures | AArch64 image and deterministic bytes | Portable image construction, not execution |
| Archive fixpoint control | Start object plus unchanged `libchain_a64.a` | Successful link resolving the transitive member | Production archive algorithm |
| Selected ET_EXEC member | Change selected `mid_a64.o` e_type at its parsed archive offset to 2 | Error identifies archive member and nonrelocatable e_type | TDD regression; predicted RED until executed |
| Later selected ET_DYN member | Change second-pass `leaf_a64.o` e_type to 3 | Error identifies archive member and nonrelocatable e_type | TDD regression; predicted RED until executed |
| Unselected member control | Change unneeded `unused_a64.o` e_type to 3 | Successful link; unselected member contributes nothing | Selection-boundary control |
| Missing definition | Omit required provider | Named undefined-symbol error, no image result | Real negative behavior |
| Duplicate definition | Supply duplicate strong definition | Named duplicate-definition error | Real negative behavior |
| Machine mismatch | Feed fixture from another architecture | Named machine/target error | Real negative behavior |
| Truncated ELF | Shorten input below a valid ELF object | Parse/link error, no image result | Real malformed-input behavior |
| PE AMD64 image | `coff_link_amd64` over checked-in Windows corpus objects, then `pe_inspect` | AMD64 PE32+, nonzero entry, deterministic image | Portable image construction, not Windows execution |

Exact implemented scenario names and fixture names must be reconciled with the
executable spec before claiming this slice complete. This table is a plan, not
a test transcript. Remaining requirement rows need additional executable
scenarios; they are not implicitly covered by these eleven cases.

The test-first continuation adds independent ELF64 program-header assertions
for file bounds, file/memory size ordering, power-of-two alignment, offset/address
congruence, readable loads, W xor X, writable data and file-backed executable
entry coverage. They apply to both direct ELF targets and the archive-linked
image. PE assertions now map the exception directory RVA to bytes, validate its
runtime-function range against executable code and check the referenced unwind
header version and complete code-slot storage. These assertions are authored,
not executed evidence; actual loader/unwind execution remains open.

## Additional test-first implementation lanes

The user's `codingtest first` instruction continues executable specification
authoring while runtime admission is pending. Production fixes still follow
observed behavioral RED; authoring further tests does not require inventing a
runtime PASS or waiting for an unrelated bootstrap to complete.

| New executable spec | Concrete cases | Requirement coverage |
|---|---|---|
| `test/03_system/app/compiler/feature/item4_linker_relocation_acceptance_spec.spl` | Full `elf_static_link` calls with ABS8 values 0/255 and overflow -1/256; PC8 values -128/127 and overflow -129/128; patch past section, invalid symbol index and unsupported relocation | ITEM4-REQ-004; byte oracle independent of production formulas |
| `test/03_system/app/compiler/feature/item4_linker_dynamic_acceptance_spec.spl` | Real shared provider and exact DT_NEEDED/imports; stripped image retains required dynamic symbols; hidden provider rejection; typed binding/runpath/hash metadata and invalid policy; embedded-NUL interpreter rejection | ITEM4-REQ-005/006/007; dynamic image semantics, not native execution |

Each mutation must prove it found the intended original ELF field or symbol
before changing it. New helpers have distinct `item4_reloc_` and
`item4_dynamic_` prefixes. The expanded image test uses `item4_read_le`,
`item4_check_elf_load_segments` and `item4_pe_file_offset`; these read wire fields
or assert mappings and never return a fabricated successful linker result.
Integration and independent review must reconcile this planned list with the
actual scenario names before submission.

## RED -> GREEN -> verification protocol

1. Commit the behavioral regression spec before implementation. Run it against
   the unchanged release-base source using a provenance-admitted pure-Simple
   runtime. Capture the failing assertion and the positive controls. Parse/import
   failures and missing runtimes do not count as behavioral RED.
2. Validate e_type on selected archive members at the hosted ELF link boundary,
   before adding them to resolution/relaxation/layout. Preserve unused-member
   behavior and member-scoped diagnostics. The SimpleOS path already validates
   every selected member through its named-object path.
3. Run the same spec after the fix, then relevant archive/ELF regression specs.
   Run each acceptance check once after it passes; at most three fix/verify cycles.
4. Generate the manual under `doc/06_spec/03_system/app/compiler/feature/` using
   the admitted SSpec/SPipe docgen path. Never put executable specs in doc/06_spec.
   Do not label a handwritten draft or source inspection as generated evidence.
5. Complete compiler/core/MCP smoke and guard checks required by AGENTS.md.
   Record real failures separately from environmental blockers. Review exact
   source/test diff and evidence before a PR to `release/1.0`; merge only after
   its actual gates are satisfied. Tags/publication are separate work.

## Runtime admission blocker, 2026-10-03

The sampled deployed `C:/dev/simple/bin/simple.exe --version` identifies itself
as the Rust bootstrap seed. It is not authorized for ordinary tests. No admitted
`bin/release` CLI was found in sampled local worktrees or WSL locations. The
separate Windows bootstrap is live, not failed: source head
`78d5a1cd7768f70cc42a56888ef3a799823bd738`, supervisor PID 26892 and compiler
PID 28048 at observation. Its unfinished Stage 2 output is not a Stage 4 CLI.
Do not restart or interfere with that session. Revalidate live handles before
waiting; historical PID values are not ongoing proof of activity.

Until a runtime is admitted, the specs and source fixes are unexecuted;
RED/GREEN, generated manuals, full verification and
release admission remain open. The existing bug
`doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md` records the
deployed-runtime problem. No completion receipt may be minted from this plan.

## Coding continuation: configured facade, relocations and lifecycle (2026-10-03)

The `complete coding` instruction retains all ten requirements. This wave adds:

- `link_request_to_native_with_config`: explicit native execution options without
  changing the frozen request record. Target vocabulary/format/ABI/width/endian,
  config agreement and ambient target disagreement are checked before execution.
  Both internal ELF and PE use the canonical typed wrapper, including its tool
  admission; unsupported Unix cross-target requests cannot produce host images.
- The fallback scenario now reaches the LinkRequest adapter itself after proving
  a real direct-link failure with fallback disabled. New facade scenarios cover
  target rejection, output preservation, bounded refusal and actual PE output.
- RISC-V CALL/CALL_PLT now validate and patch AUIPC/JALR pairs with XLEN-aware
  rounding and checked RV64 bounds. HI20/LO12-I patches retain instruction bits;
  PCREL-HI20 is supported and NONE preserves input. Twelve scenarios specify
  exact bytes, boundary errors, malformed pairs and unchanged rejected buffers.
- `LinkerLifecycleV1` owns generation-pinned provider callbacks and bounded
  session slots using the existing KPF table. Four real ELF callback scenarios
  cover replacement, stale handles, schema refusal and independent static
  recovery even when the generation table is full.

All new behavior is source-reviewed, not runtime-qualified. No admitted runtime
was found on reinspection; the earlier capped diagnostic is not retried.

### Remaining implementation, distinct from verification

| Gate | Concrete source still missing |
|---|---|
| G3 bounded execution | Windowed input/spill I/O owner and streaming engine consumers; whole-job constrained child started before allocations; no-swap enforcement; truthful measured accounting wired into receipts. Existing planners and CRC frame metadata are not an executor. |
| G4 Mach-O | Internal executable/archive/relocation/dyld link driver. Existing writer emits relocatable objects only. |
| G4 FreeBSD | Internal target-aware CRT/sysroot/libc admission; current internal ELF route is explicitly Linux/glibc. |
| G4 RISC-V | Paired PCREL-LO12 resolution, remaining branch/JAL/store-low/GOT/TLS/dynamic families, ELF machine/layout admission and RV32 image writer. |
| G5 complete lifecycle | Actual dynamic-pack loading/production command integration and loader reachability evidence. New callback/session owner does not claim those paths exist. |

PE ARM64 core linking exists, but its checked-in real fixture is a relocation
census object; a complete real executable corpus and native evidence remain.
Full compiler/application corpora, platform execution, bounded parity/performance,
modern SSpec execution, generated manuals and core/MCP checks remain unrun.

## Streamed ELF COMDAT acceptance (2026-10-04)

Existing requirements: ITEM4-REQ-003/004/009. Executable authority:
`test/03_system/app/compiler/feature/item4_stream_comdat_spec.spl`.
All scenarios remain UNRUN until an admitted self-hosted runtime is available.

| Acceptance unit | Real fixture action and required observation |
|---|---|
| Whole-group selection | Reverse two objects with the same local signature; selected code/data/RELA all come from the first group, with no losing marker |
| Live symbol resolution | Retained global references bind selected definitions; ordinary strong duplicates still reject and preserve output |
| Undefined and archive policy | Losing-only undefined references link; their undefined records can still extract an archive provider; discarded definitions alone create no new demand |
| Group lifetime | An archive member selected for another definition loses its duplicate group; retained references to discarded locals reject |
| GOT integration | Losing group relocations create no GOT entry; retained group relocations resolve real slots and targets |
| Generic groups | Flag-zero groups remain live even when signatures match; COMDAT flag-one deduplicates |
| Malformed metadata | Mutate actual group words/headers, signature and member relationships; reject out-of-bounds, invalid flags, duplicate ownership and inconsistent relocation membership |
| Bounded failure | Charge group scans, observe cancellation and preserve the destination on quota/output/scratch failures |

The fast ELF path explicitly lacks COMDAT deduplication, so it is not the oracle.
Independent program-header/byte observations and recorded GNU fixture experiments
support the contract. Stream output omits nonallocated debug sections; GNU's
retained-debug undefined-reference errors are not claimed as stream behavior.
The first executable intent was committed before implementation. Source-review
corrections are not observed runtime RED/GREEN. Peak RSS and rescanning latency
remain separate unverified NFR gates.

## Owned worker acceptance still required

ITEM4-REQ-009 requires real kernel/worker observations, separate from the new
resource-evidence fixture tests. Before the first linker input allocation, the
worker must independently observe its admitted scope, memory.max and swap.max=0.
Missing capability must preserve launch/input/output sentinels. A descendant-only
touched allocation must breach the aggregate cap with a kernel event delta;
exit 137 alone is not evidence. Peak must come from the same owned scope before
cleanup. Cancellation must kill/reap descendants, empty the scope and preserve
the prior output while removing scratch. Finally, run an actual streamed link
under that worker and prove successful output plus transactional failures under
output/scratch pressure. All these worker scenarios remain pending implementation
and execution; parser fixtures do not close them.

## Native test generated-source authority prerequisite (2026-10-04)

Status: implementation underway; all behavioral execution **UNRUN**. This is a
verification prerequisite for existing item4 requirements, not a replacement or
completion claim for any linker, SDK, host or resource requirement. The pending
[detail design](../../05_design/compiler/linker/native_test_generated_source_authority_2026-10-04.md)
records the current OS-temp entry and restricted source-root mismatch. The
[execution gate](../../06_spec/03_system/app/compiler/feature/item4_linker_execution_gate.md)
retains qualified-runtime and nonvacuous-result obligations.

Initial intent `b83b2acb980` creates
`test/01_unit/lib/test_runner_native_source_authority_spec.spl` before source
implementation. It calls the real wrapper, staging owner, coordinator request
parser and compile-argument builder. Three scenarios are initially authored;
invalid-input and cleanup-retry followups are planned. Counts describe authorship,
not executed examples or evidence that every obligation below is implemented.

| Acceptance obligation | Required observable evidence |
|---|---|
| Source staging | Transform a genuine `_spec.spl`; preserve exact transformed bytes in unique nonignored `test/native-generated-*/entry.spl` paths beneath the validated checkout |
| Ownership and cleanup | Keep-artifacts retains the stage; cleanup removes only its exact file and directory, preserves another stage, and exposes failure so cleanup can be retried |
| Coordinator request | Parse one `--refresh-source-authority`, strip it from downstream arguments, reject duplicate or internal-worker requests, and preserve ordinary inherited requests |
| Canonical closure | Coverage and explicit AOT use the staged entry plus canonical default source roots, without the hardcoded `--source src/lib` restriction |
| Fresh immutable authority | In a qualified integration run, a prior snapshot lacks the generated entry; coordinator refresh acquires a new generation containing it while preserving the prior generation and parent runner bindings |
| Inventory lifetime | Real canonical inventory observes creation/deletion; missing, ignored or outside-scope entries fail closed; compatible caches and journals are not manually rewritten |
| Native harness result | Correct `_spec.spl` positive/assertion-failure fixtures produce a real executable and expected nonzero example summary; a deliberate compile-negative `fn main` fixture remains plain `.spl` |

The frozen implementation interfaces are `native_test_stage_source_v1` and
`native_test_cleanup_source_v1` in the new standard-library staging owner, plus
`native_build_authority_request_v1` in the CLI coordinator. Unit parser/argv
assertions do not prove real snapshot refresh, child environment isolation,
inventory updates, compiler imports or native execution. Those integration
obligations remain open until independently evidenced. No new diagnostic retry
or runtime qualification follows from this plan linkage.
