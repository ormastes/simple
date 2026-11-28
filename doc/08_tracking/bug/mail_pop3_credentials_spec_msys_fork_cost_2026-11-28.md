# mail_pop3_credentials system spec gives no verdict on Windows/MSYS (fork cost)

- Status: open
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
| protocol | 613s (output was piped to tail; completion not separately confirmed) |
| credentials | 917s (the harness wrapper used `timeout 900`, so this is a timeout, not a completed run) |
| transport | 920s (also hit the harness `timeout 900`; timeout, not a completed run) |

Six further probes (recovery, config, repair, environment, placeholders, attachment) were not run.

## Not done, on purpose
Budget not raised and no example skipped (no owner approval). A real fix is a port of the
client's config/format/inbox parsing to in-process Simple, which needs a newer binary than the
stale seed; no binary was redeployed.

## Measurements that pin the cost (2026-11-28, host loaded by concurrent gates)
- One empty `$(true)` fork under MSYS: about 340 ms (10 forks = 3.4 s).
- `bash tools/mail-cli/bin/mail --help` alone, which does no mail work: 31.6 s, so an estimated
  90 forks (31.6 s divided by 340 ms; estimated, not counted) of fixed startup cost per client invocation. The probes run the client dozens of
  times per mode, so startup, not the per-step logic, dominates.
- The probes already run as one bash process per mode; batching probe calls cannot help
  because each probe step must still invoke the client.

## Concrete fix plan (bash-only, needs no new binary; not yet implemented)
1. `tools/mail-cli/bin/mail:33-38`: replace the four `$(cd ... && pwd)` / `dirname` / `readlink`
   substitutions with parameter expansion (`${SELF%/*}`) and `cd -P` plus `$PWD` via `printf -v`.
2. `tools/mail-cli/lib/config.bash:16-18` (`mail_expand_path`, `dirname`) and the per-field
   loops near lines 501-572: return values through `printf -v`/globals instead of `$(...)`,
   and read all account fields with the single existing `jq` call.
3. `tools/mail-cli/lib/format.bash` (22 external-tool uses: `sed`, `tr`, `date`, `wc`, `head`,
   `od`): replace with bash builtins (`${var//}`, `${var,,}`, `printf '%(%s)T'`, `read -r`),
   and compute `date -R`/message-id lazily only in the send path, not at source time.
4. Source libs lazily per subcommand (`lib/inbox.bash`, `lib/send.bash`, `lib/auth.bash`
   only when the subcommand needs them), so `pop3`/`credentials` probes skip about two thirds of sourcing.
5. Target: client startup from about 90 forks to fewer than 15; re-time with
   `bash tools/mail-cli/bin/mail --help` (goal under 5 s here) and then each probe mode.
Acceptance: all nine examples pass unchanged within the runner budget.
