# Windows journal and credential native export admission

Status: **OWNER APPROVAL RECORDED; INTEGRATED ADMISSION REVIEW PENDING**.
On 2026-11-15 the owner instructed: “after astra review lands pendings.”
The integration owner explicitly scoped that instruction to the previously
proposed, reviewed Windows foundation and the exact nine exports below, and
reported that interpretation in the conversation. It authorizes no additional
exports, runtime qualification, campaign restart, tag or publication. This
nine-export scope supersedes the earlier eight-export journal-only request.

## Exact scope

The existing C-private handle registry owns the tokens, generations, retained
handles and lock used by these operations. Simple retains domain policy,
enrollment, signatures, journal transitions, resource admission and credential
protocol semantics. Exposing raw handles to replace these private operations
would weaken that boundary. Existing `rt_alloc`/`rt_free` are reused.

| Proposed C-only export | Operation |
| --- | --- |
| `rt_windows_journal_open_v1` | Open the root-bound journal store and writer ownership. |
| `rt_windows_journal_live_v1` | Check the exact retained store generation. |
| `rt_windows_journal_read_v1` | Read bounded data through the retained store. |
| `rt_windows_journal_publish_v1` | Publish immutable store-relative data without replacement. |
| `rt_windows_journal_replace_v1` | Replace the permitted writer lease record. |
| `rt_windows_journal_compare_replace_v1` | Compare and replace the checkpoint reference under the store lock. |
| `rt_windows_journal_consumption_claim_v1` | Consume an exact single-use native publication receipt. |
| `rt_windows_journal_close_v1` | Close the exact store owner with explicit retained/stale outcomes. |
| `rt_windows_private_stage_discard_v2` | Retire only an exact created stage or its retained cleanup resources. |

The stage operation distinguishes actual stage deletion, handle closure with a
published destination preserved, and cleanup where no stage handle was acquired.
It never deletes by a reopened lexical path. Stale authority stays quarantined;
cleanup does not upgrade an unknown credential publication outcome.

## Concrete review evidence

The 27-file journal/host foundation was independently Astra-reviewed at bundle
SHA256 `1902626e76e591c087a1aa28cdc8d1e5bf7884add5c0d477e7f493804a0f9584`.
It remains frozen in the worktree index, separate from subsequent working-tree
implementation. See `windows_host_composition_v3.md`, Native boundary proposal.

The credential/stage package was independently Astra-reviewed after correction
of pending-only cleanup and stale-token retry handling. Its exact source and
dependency hashes are recorded in
`../09_report/windows_credential_v2_source_freeze_20261114.sdn`.
The reviewed discard header SHA256 is
`d1eecba1a21e4bfb048be7d09ff89c436aabfc9f3f9ac51948e754eac09d7905`.
No remaining P0/P1 was found in either scoped source review.

## Policy and remaining gates

`scripts/check/check-rt-dual-implementation-ratchet.shs` requires:

> Adding a row is a policy decision: it needs the repo owner's approval, named in the row's reason.

The recorded pending-landing instruction is being applied only to these exact
nine C-only OS ownership primitives after their independent Astra source review.
The candidate adds explicit named allowlist reasons; it does not regenerate or
weaken the baseline, exempt other symbols, or suppress stale-entry checks.
Integrated source and guard validation are still required before merge.

Tests, native compilation, emitted ABI validation, Windows failure injection
and full service qualification remain **NOT_RUN / NOT_COVERED** as recorded in
the respective manuals. Approval does not convert them to passing evidence,
authorize a runtime campaign restart, or authorize release publication. Each
integrated PR still requires current source review and applicable passing gates.
