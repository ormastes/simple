# Item 4 implementation and test completion ledger

Date: 2026-10-03. Integration base: `94a16103a5baeefad8bc7688e70b43b75dcf2914`.
Scope: the existing ITEM4-REQ-001..010 and linker G0..G6 requirements.
Owner: `/root`. This is an execution breakdown, not a reduction of requirements.

**Phase 4 is NOT READY.** Authored tests are not executed tests. Source-only
integration does not close verification or authorize publication.

## 2026-10-04 continuation

The next bounded-engine step is the ordinary static x64 GOT family, currently
rejected by the stream emitter. It requires real canonical GOT slots, a
synthetic base, local/global identity separation, checked relocation operands
and windowed slot emission after common storage. Merely accepting relocation
widths would be incorrect. Separate test, implementation and research worktrees
cover types 3, 9, 25–31 and 41–43, including GNU assembler's undefined GOT anchor.
TLS/dynamic relocations and whole-job enforcement remain separate open work.

Common-symbol support is now authored through the existing file-backed
entrypoint. Its test-first contract covers independent
maximum size/alignment coalescing, regular/common/weak precedence, canonical
aligned writable zero storage, real relocations and archive selection. All
additional scans must consume the work budget and observe cancellation; output
and scratch failures must preserve the destination. This removes an explicit
semantic refusal, not the missing whole-job enforcement gate. Shared plans and
parallel owners are recorded in the agent-task ledger; source and execution
status is tracked in `item4_stream_common_2026-10-04.md` under verification.
The fast archive path also now distinguishes unresolved demand from tentative
demand: a common-only provider satisfies the former without extracting further
common/weak members, while a later strong definition can replace it. An executed
GNU ld fixture experiment supports this contract; Simple execution remains UNRUN.

ELF byte-source implementation and nine acceptance scenarios are now authored.
File adapters require a four-operation seal and consume the selected reader before the
same owner's relocation/layout/writer operations. Array-input APIs keep their
existing three-operation contract. Hosted library classification and linking
must use the same retained callback bytes, while existing image publication and
configuration behavior are preserved. Portable reads preserve supported hosts
and symlinks; hostile-path snapshots and change-during-read identity guarantees
remain open rather than being inferred from path strings or caller digests.
The scenarios cover one source/writer owner, missing source, invalid inputs,
alias precedence, hosted archive snapshot reuse, canonical parity and source
failure preserving output, missing/mismatched source admission and reordered
receipt bindings tied to real output. All nine remain UNRUN. See
`doc/08_tracking/verification/item4_elf_byte_source_2026-10-04.md`.

Static ELF operational composition now seals actual relocation-field, layout
and image-writer callbacks and routes existing linker entrypoints through those
selected callbacks. Eleven authored scenarios inspect observable output changes
and errors at each boundary, missing/duplicate facets, callback/offer mismatch,
provider permutation, wrapper policies and malformed callback results. The
writer must preserve selected layout metadata, and synthesized header symbols
follow the selected header load base. Execution remains UNRUN; see
`doc/08_tracking/verification/item4_elf_operations_2026-10-04.md`.
This is an in-process structural binding, not dynamic artifact trust, byte-source
binding, full relocation ownership, bounded-memory admission or Phase 4 evidence.

RV64 initial-exec TLS source now classifies R_RISCV_TLS_GOT_HI20, allocates a
TLS-offset GOT entry independently of ordinary address entries, resolves paired
PCREL_LO12 through its high relocation, and emits the thread-pointer offset.
It also preserves the winning definition's symbol type and includes PT_TLS
alignment residue in both IE and LE offsets. Test-first acceptance inspects
linked instruction targets, GOT values and PT_TLS, archive selection and
malformed inputs; three resolver scenarios cover the prerequisite type repair.
Independent core source review found no P0/P1. All execution remains UNRUN.
Static IE does not close RV32, dynamic TLS or relaxation. See
`doc/08_tracking/verification/item4_riscv_initial_exec_2026-10-04.md`.

Terminal provider shutdown follow-up: four generic retirement scenarios and two
mapped-provider shutdown scenarios are authored before implementation. Shutdown
now retires the active generation without allocating a replacement, closes owned
sessions, retains failed cleanup owners for retry, and rejects new work once
closing starts. Independent source review found no P0/P1. All six scenarios
remain UNRUN; real unload-failure injection, CLI/trust/seal integration and the
full platform corpus remain open. This source slice does not make Phase 4 ready.
See `doc/08_tracking/verification/item4_provider_shutdown_2026-10-04.md`.

Configured provider follow-up: V2 argv transport now preserves all 15 native
configuration fields, the command uses the actual configured adapter, and
lifecycle dispatch/recovery retain that context. Thirteen new scenario
declarations cover six transport cases, six actual mapped-provider positive
cases and legacy-callback refusal. All remain UNRUN. The hosted x64 main object
is an independently compiled test fixture, not a successfully linked product.
See `linker_configured_dispatch.md` and `linker_pack_native_config_v2_2026-10-04.md`
under doc/05_design/compiler/linker for boundaries and remaining authority work.

Canonical stream follow-up: four owner-state scenarios are authored before
the core migration. Mutating operations now have an authored single-owner method
contract, builder tag writeback and explicit parent-frame writeback. Integration
and review evidence is recorded in
`doc/05_design/compiler/linker/semantic_stream_owner_dependency.md`.
The previous production-caller claim was corrected: the declaration issuer
contains future-use comments only and remains unavailable pending five live
capabilities. Primitive repair must not be reported as issuer activation.

The previous turn made progress by landing source/test slices. Current runtime
audit still finds no admitted SSpec runner: candidate SHA256
`aaf13da5942425e19b1aba2ed4b6d272687de1d4710ad7200ed0621d96990879`
has `OBSERVED_NATIVE_LINK_PASS_UNADMITTED`, qualification UNRUN, and no live
Windows Simple process. No capped build was retried.

SHA stream mutable methods, caller migration and five new scenario declarations
are now authored. See `doc/05_design/compiler/linker/sha_stream_owner_dependency.md`.
Independent source review and external expected-vector checks do not prove
compilation or execution. Core/MCP/native, SCV hydration, coverage and generated
manual gates remain UNRUN. The outer canonical compiler stream needs a separate
owner repair recorded in the 2026-10-04 bug; that follow-up is now source-repaired
and reviewed, with native validation still UNRUN.

Provider completion now has six concrete positive scenarios, production routing
and manifest requirements in `doc/05_design/compiler/linker/linker_provider_positive_acceptance_2026-10-04.md`.
The original six production-composition obligations remain open. New positive
provider API specs require actual image/exit results but do not exercise CLI,
manifest trust or sealed operation bindings. The existing unsupported-architecture
native test cannot satisfy them. All original eight rows below remain in scope.

| Item | Implementation to finish | Executable test obligations | Owner / state |
|---|---|---|---|
| Input and archive contracts | Retained ELF subranges, ar member iteration, checked member selection without whole archive reads | Malformed/truncated members, long names, padding, child lifetime, selected-member identity | Research / in progress |
| Bounded engine | File-backed symbol resolution, archive closure, layout, streamed relocations and image emission | Fast/bounded byte parity, duplicate/weak/common symbols, archive order, relocation edges, cancellation and cleanup | Research / in progress |
| Enforced resource execution | Constrained child before allocation, no-swap admission, peak accounting wired to receipts | Limit breach, unavailable enforcement, scratch exhaustion, cancellation, realistic RSS/performance | Root integration / open; UnsupportedBudget retained |
| Hosted Mach-O | Dyld commands, imports/GOT/stubs, rebases/binds, TLS/TLV, unwind, signing | Independent bytes and real provider fixtures, malformed commands, Darwin execution and signing validation | Runtime / in progress |
| RISC-V completion | ISA attributes, instruction relaxation, RV32 images, dynamic/TLS relocations | Attribute conflicts, PC changes after relaxation, RV32 boundary values, provider imports/TLS, native execution | Acceptance / in progress |
| Provider lifecycle | Actual pack admission, ABI/schema/composition agreement, retained operations, generation replacement/unload, production routing and static recovery | Real loaded provider calls, stale/pinned generations, admission rejection, failed cleanup, independent recovery | Root / in progress |
| Platform/product acceptance | Complete PE ARM64 and FreeBSD corpus, complete compiler/application links | Host loader execution, imports/unwind, startup, full corpus and linker comparison | Root integration / open |
| Phase 4 evidence | Canonical manuals, requirement trace, coverage, core/lib/MCP checks, NFR results | Every scenario executed; required branch coverage; no stubs; exact-head independent review | All owners / blocked on qualified runtime and preceding source gaps |

## Implementation order before Phase 4

| Item | Code already written (execution still UNRUN) | Next implementation and test pair |
|---|---|---|
| 1 | Retained subranges and file-source dispatch | Complete archive member identity/lifetime handling; test truncation, long names, padding and child lifetime |
| 2 | Resident ELF operation selection and a bounded x64 subset | Complete bounded symbol/archive/relocation semantics; compare complete images with the fast path |
| 3 | UnsupportedBudget refusal | Implement constrained worker admission before allocation and peak accounting; test breach, cancellation, scratch exhaustion and RSS |
| 4 | Partial hosted Mach-O | Complete TLS/TLV, unwind and weak/reexport handling; test independent bytes and Darwin loader/signing behavior |
| 5 | RV64 static IE/LE TLS and symbol-type propagation | Implement RV32, relaxation/PC remapping and dynamic TLS; test boundaries and native execution |
| 6 | Configured mapped-provider calls, shutdown, three/four-operation ELF seals | Wire trusted manifest authority and actual CLI dispatch; test real admission, replacement, pinned unload and recovery |
| 7 | Partial platform fixtures | Complete PE ARM64/FreeBSD compiler and application links; test loader startup, imports and unwind against reference outputs |
| 8 | Authored specs and source reviews | Qualify the runtime, execute specs and docgen, collect coverage/core/lib/MCP/NFR evidence; only then decide Phase 4 PASS |

Items are separate acceptance units. Source-only commits do not close their
rows. The current file-source work advances items 1 and 6; its resident cache
does not satisfy item 2 or resource enforcement in item 3. These are existing
requirements, not newly selected scope.

### Completion rule

1. Specify concrete input/output behavior and write executable tests first.
2. Implement the production caller path; an unused helper does not close an item.
3. Review failure paths, ownership and requirement/test links. Keep manuals honest.
4. Execute with an admitted self-hosted runtime when available. Record UNRUN
   otherwise; missing-runtime failure is neither behavioral RED nor GREEN.
5. Mark code-written separately from verification-ready. Only mark an item ready
   when its implementation, tests, manuals and required evidence all exist.

No repeated runtime build attempt is included: the earlier three diagnostic
attempts reached their cap. A newly admitted runtime is an external-state change;
its identity must be established before resuming execution. No Rust seed fallback.

## Ownership and review

The three existing isolated agents own the rows shown above; lower-model sidecars
are N/A. Root owns common plan/design, integration adapters and final merge.
Helper prefixes are `item4_bounded_`, `item4_macho_hosted_`,
`item4_riscv_`, and `item4_pack_`; scenario steps use `std.spec.step`.
Independent source review precedes PR integration. Phase 4 PASS additionally
requires actual runtime evidence and cannot be inferred from source review.

## Source review findings in this continuation

- Provider dispatch uses a real shared-library entry and canonical provider
  loader, explicit owned pin/close transitions, generation-retained operations,
  and the production native request adapter. Review corrected two contract flaws:
  hard budgets reject before dispatch, and policy identity hashes the full policy
  rather than echoing its schema digest. Actual mapped-provider execution is an
  authored Linux native spec, still UNRUN.
- Streaming review found value-owner mutations discarded across free-function
  calls. Retained files, archive cursors, spill states and stream traversal are
  migrated together to explicit owner transitions, including SCV consumers of
  the same file API. The repair passed independent source review; runtime proof
  is UNRUN, so this does not admit the complete bounded engine.
- Hosted Mach-O import/rebase/signature source is reviewed for its implemented
  subset. Local TLS, unwind, weak/reexport and platform gates remain explicit in
  its dedicated matrix.

All code-written status is provisional until integration review. This ledger
does not mark any previously UNRUN criterion as verified.

## Integrated source outcome

| Slice | Implementation and authored tests | Phase 4 state |
|---|---|---|
| Retained x64 candidate | Archive views, selected inputs, layout, relocation windows, checked publication; eight scenarios | Source reviewed; execution UNRUN; enforcing worker and full semantics missing |
| Mutable file ownership | Persistent read/write/close and spill/stream owners; native owner and migrated SCV scenarios | Source reviewed; execution UNRUN |
| Hosted Mach-O subset | Eager import/TLV bindings, rebases, loader commands, stubs, ad-hoc signature; nine scenarios | Source reviewed; Darwin execution UNRUN; complete TLS/unwind/reexport work missing |
| RV64 attributes and TLS | Checked attribute merge plus local-exec TLS and cross-target TLS symbol offsets; ten scenarios | Source reviewed; execution UNRUN; RV32/dynamic/relaxation gates missing |
| Native provider lifecycle | Actual exported provider/command, wire, digest-bound invocation and generation-owned unload; transport/refusal/native specs | Source reviewed; execution UNRUN; full composition/CLI and successful mapped-link corpus missing |

Additional concrete blocker:
`doc/08_tracking/bug/sha256_stream_value_owner_state_2026-10-03.md` records
pre-existing SHA streaming state loss found in SCV dependency review. It requires
its own API/caller repair and regression execution. One-shot pack/signature SHA
is a different path. No SCV hashing or hydration PASS is claimed.

Read-only runtime reinspection found no deployed `bin/release` executable and
the known candidate still reports `admission=UNADMITTED`, despite child exit 0.
No further diagnostic build or unauthorized Rust seed test was attempted.

## Historical main-only scope before reconciliation

This earlier forward-port note is retained for provenance. The reconciled tree
includes the release-only SCV callers and their retained-owner migrations.

## Main forward-port scope

Main base: `f2423274600ffe7beef03e2bf07fcf8bba310db7`. The release-only SCV
retained-file facade, hydration source, hydration spec and hydration fixture do
not exist on this branch and are not introduced by this forward-port. Their
existing release consumers were migrated on release/1.0. Shared retained-file
regressions use direct stdlib imports and private temporary files on both
branches. References to that SCV caller chain in the SHA bug/report describe the
release-side dependency; they do not assert those paths exist on main.
