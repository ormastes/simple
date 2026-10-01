# macOS bootstrap lock cleanup must remain measurable

Status: fixed; focused tests passed. Full bootstrap was not run for this fix.

## Failure and scope

The Stage-2 run at `0e3f5af9d5651b16c0cfc0f46d73aa9b22e30456` failed with
SIGILL (a separate compiler issue), then exited 2. Its EXIT cleanup called
`portable_lock_release` → `portable_lock_handle_is_owned` →
`portable_lock_actual_process_identity` → `portable-hardlink-lock.pl
owner-snapshot` → `process_snapshot` → three `ps_value` calls.

The strict RSS observer caught live Darwin `ps` PID 58209, parent 58208,
bootstrap parent 49446, PGID 49446, SID 49445, effective UID 0 and real UID 501.
Its matching birth identity was `1790082380:13043`; libproc returned EPERM.
The correct fail-closed result was outer exit 89, `rss-measurement-failed`,
`quiescent=1`. Evidence: restart worktree
`build/evidence/macos-enforced-bd544/stage2-sigill-0e3f5af/console.log`, line 64.

## Fix and safety

Guarded Darwin portable-lock identity checks now use the watchdog's admitted
native `--identity` helper, verifying its SHA-256, regular-file identity and
absence of symlink/setuid/setgid bits. Each invocation bounds output to 256
bytes and time to five seconds, killing/reaping failed children. Microsecond
birth identities must agree before and after kernel `getpgrp(pid)`. Lock
manifests retain the existing C-locale lstart hex encoding. Failed admission
does not fall back to privileged `ps`.

No cap, RSS selection, permission-denial handling, session rule, lock inode
check or stale-group recovery is weakened. Linux/MSYS and unguarded standalone
identity backends stay unchanged. SHA support loads only on the guarded Darwin
path, preserving compatibility with minimal Linux Perl installations.

The stat/hash then path-exec sequence retains the existing progress watcher's
trusted admission-storage assumption; it does not claim atomic protection from
concurrent same-user path replacement. MSYS was not live-tested in this lane.

## Focused verification

Worktree: `/Users/ormastes/simple-tmp/macos-cleanup-native-observer`.

- New `test/01_unit/scripts/portable_process_lock_macos_observer_test.shs`:
  baseline reproduction invokes the ps sentinel and fails ownership (exit 70).
  Patched run under the real enforced watchdog preserves exit 2, removes the
  owner lock, rejects foreign releases, retains live mismatched-birth groups,
  and never invokes ps inside containment. Existing success/failure EXIT and
  snapshot-error tests pass. Native and actual standalone ps manifests match.
- Missing/hash-changed/symlink/setuid/setgid observers fail closed. Malformed,
  oversized, nonzero-exit, microsecond-reused, and timed-out identity fixtures
  are rejected; the timed-out child is gone.
- Final evidence: `build/evidence/cleanup-observer-final/`. Watchdog complete,
  exit 2, quiescent 1, 8 samples, peak RSS 9,008 KiB, maximum sample 3.018 ms,
  maximum sample gap 106.902 ms, zero observer errors/restarts. Mean warm owner
  snapshot 11.989 ms over 20 invocations (includes process startup/hash checks).
- Linux Docker `simple-rdoc-lane:bookworm`: existing
  `portable_process_lock_exit_owner_test.shs` PASS. This test caught the initial
  eager SHA import; the final lazy import avoids that new Linux dependency.
- No compiler sources or runtime semantics changed; no heavy build, bootstrap,
  source integration, deployment or push was performed.

Independent Astra review: STATUS: PASS for implementation, final fixtures,
retained evidence and documentation; no blockers. Focused validation required
two fix cycles. Working/staged environment and artifact-name guards passed;
`doc/06_spec` contains zero executable specs.
