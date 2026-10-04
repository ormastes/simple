# Item 4 implementation and test completion ledger

Date: 2026-10-03. Integration base: `94a16103a5baeefad8bc7688e70b43b75dcf2914`.
Scope: the existing ITEM4-REQ-001..010 and linker G0..G6 requirements.
Owner: `/root`. This is an execution breakdown, not a reduction of requirements.

**Phase 4 is NOT READY.** Authored tests are not executed tests. Source-only
integration does not close verification or authorize publication.

## 2026-10-04 continuation

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
owner repair recorded in the 2026-10-04 bug.

Provider completion now has six concrete positive scenarios, production routing
and manifest requirements in `doc/05_design/compiler/linker/linker_provider_positive_acceptance_2026-10-04.md`.
These are planned obligations, not implemented or passing tests. The existing
unsupported-architecture native test cannot satisfy them. All original eight
rows below remain in scope.

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

## Per-item completion rule

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
