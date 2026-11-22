# Stage 2 compiler-tests RSS cap priced from ballooned free RAM, and its kill reported only as exit 88 (W21)

Date: 2026-11-22
Host: DESKTOP-VMF96U6 (Windows 11, Hyper-V dynamic-memory guest, 64 GiB, #8931)
Ledger: `C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md` W21
Branch: `work/bootstrap-rss-cap-windows-20261122` (base `origin/release/1.0.0` @ d472feffa55)

## Symptom

`admit-built-stage2-compiler-tests.shs` (P4 lane, fresh Phase 2) logged:

```
admit-stage2: tree RSS cap 11638710 KiB, build-threads=1 (... host budget 11638710 KiB
(3/4 of available 15518280 KiB; host RAM via proc-meminfo) ... bound small-host-one-worker ...)
...
status=rss-cap-exceeded  max_rss_kib=11638710  peak_rss_kib=11689776  ... (100-line body)
timeout_signal=job-terminate
admit-stage2: REJECTED (status=88); log: ...
```

The full-CLI build was killed at `surface_freeze` after 984 s. The only
operator-visible verdict was `status=88`, and the body's last line,
`timeout_signal=job-terminate`, read as a timeout.

## Root causes

1. **Budget trusts instantaneous free RAM on a ballooned guest.**
   `scripts/bootstrap/lib/tree-rss-policy.shs:888` (pre-fix) clamps the
   whole-build budget to `3/4 x host_available_kib`, and `:908` does the same
   in small-host mode. MSYS `/proc/meminfo` has no `MemAvailable`, so
   `MemFree` (15518280 KiB of a 66865260 KiB host, the Hyper-V balloon) set
   an 11.1 GiB cap: below the 31 GiB price of one full-CLI worker.
2. **A cap kill is not named.** `scripts/resource/process-tree-rss-watchdog.pl:1060`
   (pre-fix) hardcodes `timeout_signal=job-terminate` in every Windows Job
   receipt. `:1622` prints the receipt body but no verdict line. The campaign
   owner (`scripts/bootstrap/bootstrap-verification-campaign.shs:159-163`,
   pre-fix) only records `timeout` and `interrupted`, so a campaign cap kill
   wrote no summary row. `admit-stage2: REJECTED` printed only the exit status.

## Fix

- `whole_build_plan`: on Windows (`MINGW*|MSYS*|CYGWIN*`), when available RAM
  is below half of physical RAM, the budget uses physical RAM minus the host
  reserve. `bootstrap_tree_rss_host_reserve_attributed` resolves that reserve
  in this order: `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`, then
  `SIMPLE_HOST_MEM_RESERVE_FREE_MIB`, then host config `mem_reserve_free_mib`
  (2048 on this host), then the default. The plan summary names the
  substitution and the reserve source. On this host the cap becomes
  32505856 KiB (one worker, bound `worker-floor`).
- The guarded two-worker floor still uses the measured value, so a
  substituted number can never widen it.
- An explicit `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` is still kept as-is.
- `BOOTSTRAP_TREE_RSS_TEST_PLATFORM` is a test hook and needs
  `BOOTSTRAP_TREE_RSS_TEST_FIXTURE=1`.
- The watchdog prints `rss-guard: rss-cap-exceeded cap_kib=<n> peak_kib=<n> (... not a timeout ...)`
  after the body. The Windows receipt now records `termination=job-terminate`.
  It sets `timeout_signal=job-terminate` only for a real timeout, and
  `timeout_signal=none` otherwise.
- `bootstrap_tree_rss_cap_kill_line RECEIPT` is the shared parser for cap kills.
- `bootstrap_verification_campaign_record_cap_kill` appends
  `task=campaign_rss_cap|result=FAIL|status=88|kill_cause=...` and prints a
  stderr verdict.
- `bootstrap-phase-verification.shs` relays a row watchdog's `rss-guard:` line.
- The admit script prints `admit-stage2: REJECTED (status=88, rss-cap-exceeded cap_kib=... peak_kib=...: killed by the process-tree RSS cap, not a timeout)`
  and writes `kill_cause=` to `rejection.env`.

Scope limit: the substitution fixes only a plan whose cap stays at or below
the default hard ceiling (58720256 KiB). That is one worker on this 64 GiB
host. On a larger ballooned Windows guest (around 128 GiB), the two-worker
plan needs the elevated-ceiling admission (`bootstrap_tree_rss_admit_ceiling`).
That admission still reads live free RAM and bounds the cap at 3/4 of it, so
the lane is refused before it starts, with `available_bound` named in the
refusal. It is not killed mid-run, but it is not admitted either.

Free RAM can also be low because another lane is running. That case is
refused by admission (W23, `stage2_admit_concurrent_heavy_lane_admitted_2026-11-22.md`),
not priced here.

## Specs

- Reproducing:
  - `sh scripts/bootstrap/lib/tree-rss-policy.shs --selftest`, case
    `plan-w21-windows-balloon-physical-minus-reserve`. The incident meminfo
    gives `1:32505856:0:worker-floor`. The pre-fix code gives
    `1:11638710:0:small-host-one-worker` and fails 3 w21 cases.
  - The same selftest, case `w21-cap-kill-line kill-old.env`, which uses the
    pre-fix Windows receipt shape.
  - `scripts/check/admit-stage2-compiler-tests-lane-test.shs`, case `capkill`.
    It fails on the pre-fix admit script, which prints only `REJECTED (status=88)`.
- Generalization:
  - `w21-linux-trusts-available`: the same reading on Linux keeps 11638710.
  - `w21-windows-unballooned-trusts-available`.
  - `w21-windows-balloon-default-reserve`.
  - `w21-summary-names-balloon-source`.
  - `w21-platform-hook-needs-fixture-switch`.
  - Receipts for a phys-footprint kill, a timeout and a missing file.
  - Lane test: the campaign `campaign_rss_cap` row, and a plain failure that
    carries no `kill_cause`.

Verified: policy selftest `PASS — 122 fixture(s)`, lane test
`PASS — 17 admit-lane case(s)`. No compiler or bootstrap was run, because a
Stage 3 was live on the host. The real watchdog was only checked with `perl -c`:
its Windows session helper needs a compile.

## Workaround retired

`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=25165824` in `phase4-new.sh` is no
longer needed to size the cap. It still works as an explicit override.
