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

## Measurements that pin the cost
Correction (2026-11-28): the first draft of this doc quoted `--help` = 31.6 s and 340 ms per
fork. Those were taken while pre-push gates loaded the host and are wrong. Re-measured on a
quieter host:
- One empty `$(true)` fork under MSYS: about 36 ms (10 forks = 0.36 s).
- `bash tools/mail-cli/bin/mail --help`: 2.1 s. The startup path (`bin/mail`, `lib/config.bash`)
  holds about 10 forks, so startup is not the dominant cost; the earlier "about 90 forks"
  estimate is withdrawn.
- `pop3_credentials_probe.shs protocol` alone: 254 s, rc=0, all 10 PASS lines present
  (613 s when measured under gate load). Nine examples at that rate is on the order of 30+
  minutes, still far over a runner budget.
- Loaded-host timings for the other probes: credentials 917 s and transport 920 s, both cut
  off by a `timeout 900` wrapper, so those are lower bounds, likely inflated by overlapping gates.
- The probes already run as one bash process per mode; batching probe calls cannot help
  because each probe step must still invoke the client.

## Fix plan (not yet implemented)
The dominant cost is per-step work inside each client call, not startup. First step is to
profile one `protocol` probe step (bash `PS4='+${EPOCHREALTIME} '` xtrace of a single
`tools/mail-cli/bin/mail` call against the synthetic curl) and cut the forks that account for
the time. Candidate sites, to be confirmed by that profile:
1. `tools/mail-cli/lib/config.bash` (about 56 `$(...)`; the per-field account loop near
   lines 501-572 should use the single `jq` call already present) and `mail_expand_path`
   (return through `printf -v` instead of a substitution).
2. `tools/mail-cli/lib/format.bash` (22 `sed`/`tr`/`date`/`wc`/`head`/`od` uses) to bash builtins.
3. `tools/mail-cli/bin/mail:33-38` path resolution via parameter expansion.
4. The probe's synthetic `curl` shim and credential helper are each a separate bash process
   per call; make them cheaper (no `cat`/`printf` subshells).
Acceptance: all nine examples pass unchanged within the runner budget.
