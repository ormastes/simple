# Item 4 linker acceptance and TDD plan

Date: 2026-10-03. Target: `release/1.0` at
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a`.
Status: specification in progress; execution and certification unverified.

Implementation update, 2026-10-03: after the tests were committed, the user
instructed `fix what you can`. The hosted ELF engine now rejects selected
non-ET_REL archive members before resolution/layout and rejects embedded NUL
in a dynamic interpreter path before input processing. The existing regression
scenarios cover both changes; the interpreter scenario pins the exact error.
This is test-first authorship followed by source-reviewed implementation, not
an observed RED/GREEN cycle. Runtime execution and all broader gates remain open.

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
