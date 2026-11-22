# Stage 3 resume drops SIMPLE_MIR_SHARDING / SIMPLE_FRONTEND_CACHE at `env -i` (2026-11-23)

Status: FIXED (transport). Root cause of the shard-worker AV: OPEN.

## Problem

On Windows the Stage 3 MIR shard workers AV (`0xC0000005` at `claimed=0`)
when they read back the frontend parse cache (`.fpc`). The working
configuration is `SIMPLE_MIR_SHARDING=1` + `SIMPLE_FRONTEND_CACHE=0`
(verified 2026-11-22/23: 9/9 shards, 1612/1613 modules passed).

`scripts/bootstrap/resume-stage3-from-admitted.sh` runs the Stage 3 child
under `env -i` through `scripts/bootstrap/lib/stage3-native-build-worker.sh`,
which forwards only an explicit allowlist. `SIMPLE_MIR_SHARDING` was never
forwarded, and `SIMPLE_FRONTEND_CACHE` was hard-coded to `1` in both the args
hash and the worker transcript. The canonical lane could not use the
workaround, so the run had to be replayed by hand.

`bootstrap-from-scratch.sh`'s own Stage 3 (`stage3_build_args_sha256` and its
`bootstrap_stage3_run_transcribed` call) had the same gap.

Evidence: `C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md`
rows W24 (shard 0/9 AV at `claimed=0` with RAM free; "`SIMPLE_MIR_SHARDING` is
NOT forwarded by the `env -i` resume") and W27 (shard workers AV after `.fpc`
hits, `stage3-native-build.log:6600-6647`; workaround
`SIMPLE_MIR_SHARDING=1` + `SIMPLE_FRONTEND_CACHE=0`, `frontend_parse_cache.spl:103`).

## Fix

Validated single-variable pass-throughs, the same shape as
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM`:

- `SIMPLE_MIR_SHARDING`: unset (absent) | `0` | `1`, anything else is an
  error exit.
- `SIMPLE_FRONTEND_CACHE`: unset (pinned `1`) | `0` | `1`, anything else is
  an error exit.

Both go into the args hash and the transcribed invocation. The resume
launcher forwards them to the worker explicitly (`env VAR="${VAR:-}"` at all
four launch sites), and the worker validates them again before transcribing
(exit 64 on an invalid value). Unset reproduces the pinned argv byte-for-byte,
so existing admission receipts are unaffected. An explicit
`SIMPLE_FRONTEND_CACHE=1` is the pinned value, so it produces the same
invocation and hash as unset. No defaults change.

Files: `scripts/bootstrap/resume-stage3-from-admitted.sh`,
`scripts/bootstrap/lib/stage3-native-build-worker.sh`,
`scripts/bootstrap/bootstrap-from-scratch.sh`.

Follow-up fixes in the same PR:

- `bootstrap-from-scratch.sh` captures the caller's `SIMPLE_FRONTEND_CACHE` at
  entry. Before this, the Stage 2 cache setup (`bootstrap_cache_enable_persistence`,
  `bootstrap-cache-lineage.shs:271`) exported `SIMPLE_FRONTEND_CACHE=1` before
  Stage 3 read it, so a caller's `0` was silently replaced by `1`.
- Manifest verification (`scripts/check/lib/bootstrap-stage3/manifest-verify.shs`)
  no longer assumes the value. The focused-v5 Stage 3 vector reads
  `SIMPLE_FRONTEND_CACHE` / `SIMPLE_MIR_SHARDING` from the recorded transcript
  (only unset|0|1 is accepted). It also requires the transcript to agree with
  the manifest's new optional `focused_frontend_cache` / `focused_mir_sharding`
  fields. An absent field means the pinned value. `manifest-write.shs` writes
  those fields only when they are set, so an unset run keeps the same manifest
  bytes as before. The legacy-v4 recipe used to hard-code `SIMPLE_FRONTEND_CACHE=0`;
  it now uses the value the transcript recorded, validated to 0|1.
- Updated the test fixtures that bind every recipe variable:
  `stage3-focused-provenance-test.py` and `stage3-worker-lowering-lane-test.py`.

## Verification

`sh scripts/bootstrap/tests/stage3-mir-sharding-frontend-cache-passthrough-test.shs`
(wired as `local-stage3-mir-sharding-frontend-cache-passthrough` in
`config/check/must_check_gates.sdn`). It runs text slices of the real scripts
and compiles nothing:

- reproducer: `SIMPLE_MIR_SHARDING=0|1` and `SIMPLE_FRONTEND_CACHE=0` appear in
  the worker transcript, the resume args-hash vector equals the transcript
  vector, and the hash differs from unset by exactly that one word. The W27
  recipe reaches the transcript.
- unset: no `SIMPLE_MIR_SHARDING` word, `SIMPLE_FRONTEND_CACHE=1`, vector
  equal to explicit `SIMPLE_FRONTEND_CACHE=1`.
- generalization: five invalid spellings per knob (`2`, `yes`, `true`, `01`,
  ` 1`) are refused by both the launcher and the worker before anything is
  recorded. `bootstrap-from-scratch.sh` Stage 3 hashes and transcribes both
  knobs.

- manifest-verify, run on the real helper functions: these PASS: legacy
  manifest + pinned transcript, transcript `=0` + manifest `=0`, and the W27
  recipe recorded on both sides. These are refused: transcript `=0` with the
  manifest absent (pinned 1) or `=1`, garbage values on either side, a
  transcript missing `SIMPLE_FRONTEND_CACHE`, and a `SIMPLE_MIR_SHARDING`
  mismatch in either direction.

Result: `PASS — 30 case(s) checked`. Control: the first 17 cases run against
the `origin/release/1.0.0` scripts pass the two unset arms (pinned argv
unchanged) and fail all 15 new-transport arms.

Pre-existing failures, identical on an unmodified `origin/release/1.0.0`
worktree on this host and unchanged by this PR:
- `stage3-worker-lowering-lane-p-f-test.shs`: the "repo config default" arm
  fails because `config/host/<host>.sdn` pins `stage3_file_workers=0`.
- `stage3-focused-provenance-test.py`: 6 failures, transcript writer exit 90.
- `stage3-worker-lowering-lane-test.py`: 3 failures, stale fixture missing
  `stage3_streaming_surfaces`.
- `stage3-invocation-consistency-test.py`: 4 failures,
  `'sh' != 'fixture-stage2_admitted_absolute'`.

Observed, not changed here: the resume lane writes a legacy-v4 manifest
(`BSTAGE3_INVOCATION_CONTRACT` is unset in `resume-stage3-from-admitted.sh`).
The v4 recipe in manifest-verify omits words the resume args hash contains,
such as `SIMPLE_ABI_POLICY` and the per-file lane env. Whether the resume
lane's final `manifest-verify` can pass at all needs its own investigation.

## Still open

The `.fpc` read-back AV in the Windows shard workers is not fixed here. This
change only makes the workaround reachable from the canonical lane. See
`stage3_surface_build_av_items_spl_warm_frontend_cache_2026-11-22.md`.
