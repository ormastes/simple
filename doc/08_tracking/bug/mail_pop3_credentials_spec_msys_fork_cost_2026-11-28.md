# mail_pop3_credentials system spec gives no verdict on Windows/MSYS (fork cost)

- Status: verification-pending
- Found: 2026-11-28 (lane ft30-pop3)
- Blocked: precondition: a deployed pure-Simple `bin/simple` plus owner approval to port the mail-cli bash client to Simple, or owner approval of a larger budget for this spec on Windows/MSYS.
- Repro: `test/03_system/app/mail_cli/feature/mail_pop3_credentials_spec.spl`; prior evidence `C:/dev/wt/ft29-8-pop3.log` (rc=124) and PR #12411.

## Cause
Each of the 9 examples runs `test/01_unit/tools/mail_cli/fixtures/pop3_credentials_probe.shs <mode>`,
which invokes the production bash client `tools/mail-cli/bin/mail` dozens of times, plus a
synthetic `curl` and credential helper as extra bash processes. The client (about 3000 lines of
bash in `tools/mail-cli/lib/*.bash`) has about 230 `$(...)` substitutions
(config 56, format 38, inbox 32, send 26, auth 21, credentials 12, pop3 9, bin/mail 11),
each a fork under MSYS.

## Timings (this host, one probe at a time, bash probe invoked directly)
| probe | wall |
|---|---|
| protocol | 613s |
| credentials | 917s (the harness wrapper used `timeout 900`, so this is a timeout, not a completed run) |
| transport | not finished at filing time; at least the time elapsed since start (over 30 min) |

Six further probes (recovery, config, repair, environment, placeholders, attachment) were not run.

## Not done, on purpose
Budget not raised and no example skipped (no owner approval). A real fix is a port of the
client's config/format/inbox parsing to in-process Simple, which needs a newer binary than the
stale seed; no binary was redeployed.
