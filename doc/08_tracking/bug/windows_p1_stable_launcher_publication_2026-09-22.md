# Windows P1: stable launcher publication and recovery

Status: draft; verification incomplete. No release acceptance is claimed.

The immutable Windows generation pointer could advance while `bin/simple.exe`
still contained the previous compiler. Windows bootstrap now publishes the
sealed, digest-admitted candidate through a staged same-volume File.Replace
(File.Move for the first publication), then probes `build --help` before commit.

Journal v4 records original launcher and receipt hashes and durable backup
paths. The deploy receipt remains v3 with additive launcher fields. Existing v3
journals remain readable. Windows rollback of a receipt without launcher
metadata is refused rather than claiming that the launcher was restored.

Uncommitted Windows recovery restores launcher and receipt before restoring the
generation pointer. Missing or corrupt backups fail closed with the journal
retained. Receipt absence is restored by removing the new receipt. Backups are
copied on restoration, so interrupted restoration is repeatable. Explicit
generation rollback uses the same restoration path and preserves immutable
generation/provenance validation. Recovery binds the sealed deployment receipt
digest and rechecks authority; rollback receipts have a journal-bound digest.
Commit records a durable committed state before journal cleanup; cleanup
failure cannot turn an admitted commit into an abort request.

Each file replacement is atomic. The launcher, receipt, and generation pointer
cannot change in a single filesystem operation; recovery reconciles a process
interruption. Concurrent readers may observe the intermediate generation.
Backups remain after commit for explicit rollback. Interrupted Windows
generations remain at their original path so a second recovery can still
validate the journal; automatic retention cleanup is outside this change.

## Evidence and limits

- The predecessor's focused publisher run reached the deep-path case and
  failed there due to a stale expected hash; that assertion was corrected.
  Its earlier cases are predecessor evidence, not a final suite PASS.
- Shell syntax and PowerShell parsing passed during this continuation before
  the final review edits. The direct-env working guard passed, and executable
  specs under `doc/06_spec` counted zero.
- One new `windows_stable_journal_recovery_test.shs` control was run. It failed
  because Windows PowerShell converted a null File.Replace backup argument to
  an invalid empty path. Explicit discard paths replaced the null arguments.
  The corrected control was not rerun, respecting the lane's retry cap.
- Negative tests now require an explicit error flag and different candidate
  bytes, including exclusive destination locking and receipt publication
  failure. The new control covers missing/corrupt backups, receipt restoration
  or removal, simulated smoke failure, and commit failure. These final forms
  are not claimed to have passed.
- The journal control substitutes pointer CAS and fsync boundaries. Real
  Windows directory durability, abrupt process termination, running-image
  locking, authority-qualified explicit rollback, complete bootstrap, and
  Linux/macOS/BSD regression coverage remain required before approval.
- Windows long-path policy is unchanged; the existing deep-path test stays
  below the legacy 260-character limit. Non-ASCII path receipt encoding has
  not been qualified.

## Correctness, performance, and compatibility review

Launcher publication uses immutable generation bytes and the admitted Stage 4
digest, not a mutable build output. Recovery validates both retained backups
before modifying the launcher. Hashes use streaming reads, with memory bounded
by stream buffers; the added copies and hashes occur only during deployment or
rollback. Disk retention adds one previous executable and one previous receipt
per deployment. No latency or RSS benchmark was run.

Other hosts do not invoke the Windows publisher; shared journal v4 and commit
ordering changes still require their existing transaction regression tests.
PR #1275's `[native-build] Artifact published: <output>` receipt remains a
separate native-build completion signal. This deployment change neither parses
nor changes that line, worker exit checks, or stdout/stderr handling. Journal
value reads accept CRLF receipts. No dependency on PR #1275 is introduced.
