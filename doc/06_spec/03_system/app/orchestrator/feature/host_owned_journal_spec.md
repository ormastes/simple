# Managed host journal cleanup — authored specification

Status: **NOT_RUN / AWAITING_VERIFICATION**. Authored manual, not generated execution evidence. No builds, native commands, tests or subprocess fault injection were run. Editing/static processes used shared CPU affinity 0–4.

Source: `test/03_system/app/orchestrator/feature/host_owned_journal_spec.spl` (eight cases). Canonical dependency: owned lock/journal source `aa6668c3ea2cf39f3816488aa143305f891d809b`, source-reviewed; root owns integration. A staged host capability never substitutes a fabricated replayed journal or ledger.

| Requirement | Authored actual prevention case |
| --- | --- |
| HOST-OWNER-CLEANUP-01 | Actual generation-owned journal denies second writer and legacy close; retained lease bytes/native owner remain intact. Actual reservation-payload corruption rejects capacity projection and releases acquired writer. Actual malformed WAL CURRENT rejects replay and releases lock. Actual journal event quota rejects recovery append and closes the latest acquired writer; reopening with room retains outcome-unknown charge. |
| HOST-OWNER-CLEANUP-02 | Actual lease mismatch returns canonical retained cleanup in finite reply with Retained state and exit2. Restoring only exact fixture lease bytes permits canonical cleanup retry; result remains failed. Copied stale cleanup cannot touch the replacement writer or its lease. Forced-quarantine owned reopen retains admitted capacity and does not assert continuity. |
| HOST-OWNER-CLEANUP-03 | Actual incomplete private root rejects before journal acquisition and creates no synthetic local owner. Compiled Linux branch reaches its actual private-policy prerequisite; compiled non-Linux branch refuses POSIX runtime path before reading policy. No fake Windows host flag is injected. |

The fixture's existing signed-execution setup supplies a real admitted operation; **no provider command is invoked** by this suite. Tests acquire actual native owned locks and mutate only their private fixture files. No synthetic release state or fake filesystem failure callback is used. Full runtime outcomes, actual Windows native lock behavior, Unknown/ConsumedError OS close failures, and open-time cleanup-required caused by a real failed release are unexecuted/unqualified. Those failure states are preserved in source; this suite does not manufacture a passing kernel fault.

Legacy Result open/close APIs remain compatibility-only and do not flatten the new cleanup-bearing path. Managed finite commands exhaustively consume HostLocalRootOpenV2. A reply's `journal_cleanup` contains the only canonical retry capability; `cleanup_state` preserves Released/Retained/Unknown/ConsumedError/Stale. Only Released + closed + empty error is clean closure. ConsumedError has no retryable owner but remains an error. Unknown remains quarantined and never permits raw descriptor retry.

Caller inventory in this source tree: managed finite command migrated to owned root/open/close. Legacy root Result wrapper still uses legacy capacity open. Controller, Caret and legacy-domain owners were notified to migrate their separate worktrees and preserve host reply capabilities before any report/output failure. Actual persistent Windows roots remain a separate native-private capability prerequisite; the finite native runtime is explicitly Linux-only.
