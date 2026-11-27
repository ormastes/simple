# DAE-05 B1 assessment test plan

Status: AUTHORED / NOT_RUN, 2026-11-15. Existing build/native campaigns remain
stopped. These are actual source assertions, not execution or coverage counts.

| Required behavior | Authored scenario |
| --- | --- |
| DAE-05-H: conservative actual-owner projection | Owned Host journal returns canonical producer payload bytes and preserves revision/sequence |
| Invalid input cannot poison or select arbitrary files | Duplicate/oversized/invalid ID lists and `parent.lease` reject; a valid unknown ID selects no artifact; valid observation still works |
| DAE-05-N: observed authoritative corruption is sticky | Change actual payload, fail digest, restore exact bytes, refuse copied owner under quarantine with exact payload digest |
| Actual existing diagnostic consumer | `host-status` service emits aggregate Incomplete sample, count fields and unchanged capacity kind/sequence; provider command count stays zero |
| Determinism and bounded scope | Prepare five actual ledger reservations in unsorted order; select four expected prefix IDs and expose total five/omitted one/Incomplete |
| Legacy status compatibility | Unowned compatibility fixture emits explicit unavailable assessment, examines zero and retains old status fields |
| Strict controller old/new compatibility | Pure status checker accepts the old response and only the new optional nested diagnostic |
| No new admission authority/unknown-field tolerance | Unrelated fields and altered authority still reject despite diagnostic presence |

Specs live under `test/02_integration/lib/orchestration/` and
`test/01_unit/lib/nogc_sync_mut/orchestration/`. Their authored `.md` manuals mirror
those paths under `doc/06_spec/`. No executable spec was placed in that tree.
Frozen public/step helpers use actual production APIs; no no-op, fake pin grant,
hardcoded passing helper or caller-supplied evidence set is an oracle.

Native Windows, true concurrent schedules, provider/lock/fault injection,
power-loss/crash recovery, actual expiry/tombstones, exact deletion, generated
manual quality, maintenance scores and performance remain NOT_COVERED/NOT_RUN.
No positive expiry or GC scenario is claimed in this diagnostic slice.
