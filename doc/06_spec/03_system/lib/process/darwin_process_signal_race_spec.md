# Darwin descendant signal retirement race

Executable specification: `test/03_system/lib/process/darwin_process_signal_race_spec.spl`.

On macOS, run `sh scripts/check/check-sosix-darwin-process.shs`. The native
component exercises capture, timeout, descendant retirement, bounded output,
exit status, cancellation, and acknowledgement. A deterministic regression then
models a live process snapshot followed by EPERM from a repeated group SIGKILL.

After a successful earlier SIGKILL and an observed leader exit, repeated EPERM
retains the owner for another observation. It cannot mark the group retired,
reap the leader, freeze the result, or permit acknowledgement. Persistent denial
reaches the existing cleanup deadline and returns ETIMEDOUT while retaining
authority. An initial SIGKILL denial still returns EPERM.
After the snapshot independently reports zero live members, the regression
requires exactly one reap, a frozen result, and successful acknowledgement.

The real descendant test reproduced EPERM before the fix: `leader_exited=1`,
`kill_sent=1`, and the diagnostic follow-up snapshot reported zero live members.
The deterministic regression fails against the prior header and passes with the
fix. This is cooperative Darwin snapshot evidence, not sealed V4 admission or a
deployed P2 rebuild.
