# Historical exec child projection specification

Executable: `test/01_unit/lib/nogc_sync_mut/orchestration/host_runtime_exec_projection_v3_spec.spl`.
Requirements: HOST-02, ORCH-02. Status: **NOT_RUN**, authored manual.

| Scenario | Observable assertion |
|---|---|
| Exact reopen | Actual disk WAL and packet archive reopen to one uncertain parent, 4000 available CPU millis and 12000 available memory bytes; child remains admitted |
| Child terminal/interruption | Completed, failed, cancelled and interrupted child rows leave the same parent charge; only interrupted execution recovers to outcome-unknown |
| Signed subject substitution | Fresh Ed25519 frames independently verify; changed principal, project or environment rejects with the subject-binding error |
| Resource bounds | Re-signed memory 4001 rejects against original 4000; timeout 1000 with operation duration 999 rejects |
| Runtime/provider/scope | Canonical signed changed native CID or provider pin rejects; an internally rebound and re-signed foreign scope cannot replace the actual parent; a changed original observation scope also rejects |
| Orphan child | Complete packet archive without the actual parent WAL row rejects with OPERATION_NOT_FOUND |
| Missing evidence | Missing packet, reservation, V2 execution packet, creation or original observation and malformed packet bytes each fail real reopen |
| Unknown action | A real additional unknown action row reaches the strict original reservation matcher and rejects |
| Exact actual child | A separately signed changed operation cannot substitute for the actual retained child envelope |
| Recurrence | Read-only classifier has no recursive Host/provider/clock/effect imports and no latest-inspection substitution; the capacity branch matches exactly one known action |

Fixtures create private temporary files and the actual segmented operation WAL,
close its sole writer, then reopen through the real capacity owner. They do not
fabricate in-memory journal entries. Native identities and observations are
explicitly synthetic. Ed25519 signatures prove only fixture frame arithmetic,
not enrollment, current grant acceptance, assignment history or a live process.
Old parent grant expiry is deliberately earlier than the synthetic observation;
historical projection does not impose a current authorization clock.

All ten scenarios are authored, unexecuted. No coverage, native exec, installed
control, one-use delegation, response publication or service responsiveness
qualification is claimed. No compiler, seed or native test campaign was started.
