# SFFI-authority group 2: five guards RED from a stale-snapshot clobber

- Date: 2026-09-02
- Gate: `scripts/check/check-sffi-v2-authority.shs` (blocking push gate)
- Status: FIXED for these five guards (parent gate 18 -> 13 failing)

## Symptom

Five audits exited 1 with **zero output**:

- `scripts/audit/dashboard-remote-collector-sffi-authority.shs`
- `scripts/audit/dashboard-schedule-collector-sffi-authority.shs`
- `scripts/audit/portal-server-sffi-authority.shs`
- `scripts/audit/play-session-store-sffi-authority.shs`
- `scripts/audit/ssh-gcm-sffi-v2-authority.shs`

Each was `set -eu` plus bare `test`/`grep -q`, so the first failing assertion
killed the script before its trailing `echo ... PASS` could run. A guard that
fails with no output is how this sat RED unnoticed, forcing every push in the
repo onto `--no-verify` and bypassing all 19 push gates.

## Classification: REAL VIOLATION, not expectation drift

The hardcoded expectations were correct. The audited **sources** had been
reverted. `git log 1b4edca296c..HEAD -- <file>` shows exactly one commit
touching all five files:

    e274cd33719  chore: merge all share-history worktree branches into main

That merge is a stale-snapshot clobber, not a forward change. Evidence that it
snapshotted a tree older than *both* sides:

- HEAD is behind `1b4edca296c` (PR #75, which landed these guards **with** the
  hardened sources).
- HEAD is *also* behind `1b4edca296c^`: pre-#75 already used the
  `std.io_runtime.{file_exists, dir_list, time_now_unix_micros}` wrappers and
  already carried the portal `index_of` bug fix. HEAD reverted those to raw
  `rt_*` externs and reinstated the buggy `?? clean.length()` coalesce whose
  comment explains it sliced out of range when `?` sat at index 3.

Because only the clobber commit touched these five `.spl` files, restoring them
wholesale from `1b4edca296c` loses no forward work. Every imported symbol was
re-verified to still resolve at HEAD.

### Security regressions reverted by the clobber

`src/os/apps/sshd/ssh_cipher_live.spl` is the serious one:

1. Called the **legacy untagged** `rt_ssh_aes256_gcm_decrypt_packet(...)`
   instead of the tagged `_v2` carrier. The Rust side had *already* retired that
   symbol — all 12 Rust-side assertions of the ssh-gcm audit pass at HEAD, and
   `rt_ssh_aes256_gcm_decrypt_packet` has no interpreter dispatch entry and no
   `RuntimeFuncSpec`. So this was a **live break**, not just a style regression.
2. Deleted `_validate_gcm_wire_packet`, the bounded wire-frame admission check
   (length/tag/alignment consistency) that runs before crypto dispatch.
3. Added `serial_println` lines dumping key length, IV, nonce, AAD and body as
   hex on every encrypt/decrypt — key material to the serial console.

The other four reverted `unsafe(capabilities: [ffi])` call-site gating and, for
portal, the `read_file_text_result` Result-lift (reverting to a raw read whose
failure could not be distinguished from empty content).

## Fix

1. Restored the five `.spl` files from `1b4edca296c`. Audit expectations were
   **not** touched — bumping a count to green would have laundered the crypto
   regression above into a blessed baseline.
2. Rewrote all five guards to the verdict discipline in `.claude/rules/vcs.md`:
   verdict LAST on stdout, `PASS — <n> assertion(s) checked` / `FAIL — <label>:
   expected <n>, got <m>` naming every offender / `ERROR — nothing was checked`,
   exits 0/1/2. Non-vacuity is absolute: a run evaluating zero assertions is
   ERROR, and a missing audited file is ERROR rather than a silent pass.
   Assertions now accumulate instead of aborting, so one run reports every
   offender. Helpers are inlined per script rather than sourced from a shared
   file, because `check-guard-wiring.shs` scans `scripts/audit/` and would treat
   a shared non-guard file there as an unwired guard.
3. The portal and ssh guards additionally gained explicit `absent` assertions
   for the raw call shapes the clobber reintroduced, so this exact revert is
   caught by name next time.

## Verification

Before (all five): exit 1, no output at all.
After: all five exit 0 with a PASS verdict (4, 4, 6, 4 and 17 assertions).

Discrimination proved by injected fault, not just by a green run:

- legacy untagged ssh call reintroduced ->
  `FAIL — ...: retired legacy untagged provider call ...: expected 0, got 1` (1)
- portal reverted to raw `rt_file_read_text` ->
  `FAIL — ...: any raw rt_file_read_text call site ...: expected 0, got 1; lifted content handed to the HTTP responder ...: expected 1, got 0` (1)
- audited file removed ->
  `ERROR — nothing was checked (missing audited file: ...)` (2)

Parent gate: `18 of 46` -> `13 of 46` failing. None of the five are mine any
more; the remaining 13 are other agents' concurrent lanes.

## Follow-up

The clobber merge `e274cd33719` reverted these five files. It very likely
reverted others outside this group's scope — the remaining 13 failing guards
should be checked against the same commit before their counts are touched.
