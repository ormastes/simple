# Daemon SDK exact lock owner scenarios

Source: `test/01_unit/lib/daemon_sdk/daemon_sdk_exact_lock_owner_spec.spl`.
Manual companion; not generated execution evidence. Status: NOT_RUN.

| Requirement | Real filesystem scenario | Required result |
|---|---|---|
| DLOCK-01 | Release first acquisition; reacquire under the same PID; release first receipt again | New full record differs and remains untouched; current receipt releases normally |
| DLOCK-02 | Shut down old runner twice; start replacement; shut down old runner again | Replacement record remains; its own shutdown removes it |
| DLOCK-03 | Pass current PID to legacy release for an owned record | Refused; original record retained |
| DLOCK-03 | Acquire/release historical legacy record | Wrong PID refused; correct and repeated release succeed |
| DLOCK-04 | Hold the stable guard during owned/legacy acquisition, release (acquisitions include stale-break judgment) | Every mutation refuses; current record and guard inode remain |
| DLOCK-01 | Place a fresh empty partial record; attempt acquisition/release | Denied receipt cannot delete the partial record |

The standalone native fixture isolates lock mechanisms from the unrelated spool
hash mismatch. These authored scenarios do not claim executed tests or generated
manual admission. No release PASS is implied.
