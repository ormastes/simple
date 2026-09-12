# Stage 2 sanity fails `native-capsule-receipt-invalid` with IDENTICAL byte counts (macOS, 2026-09-12)

Status: OPEN, freshly reproduced. **Supersedes the Stage-2
`serialize_mir_function` SEGV as lane 1's Stage-2 blocker** — see "The SEGV did
not reproduce" below before scheduling any work against that older item.

## Reproduction

Host: macOS 15 (Darwin 25.5.0), Apple M4, `aarch64-apple-darwin`, repo at
`origin/main@f38ceb0f804`. The comparator workaround from
`bootstrap_stage3_comparator_rejects_homebrew_symlinked_cmp_on_macos_2026-09-12.md`
is REQUIRED to get this far:

```sh
PATH="/usr/bin:$PATH" BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp \
SIMPLE_NATIVE_INCREMENTAL=1 SIMPLE_CACHE_SCOPE=bootstrap-r2 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 \
     --full-bootstrap --mode=dynload --jobs=half
```

Timeline (this run): start 12:14:33Z; Rust seed + runtime rebuilt; Stage 1
preserved 12:15Z; `Stage 2: admitted parent -> bootstrap_main.spl`; Stage 2
native build **completed**; failed in Stage 2 sanity at 12:33:13Z. Wall ~18m.

## The failure

`.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log`:

```
scripts.check.cert.redeploy_gate.fixtures.hello_world
native-capsule-receipt-invalid
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
[native-compile-failed] scripts.check.cert.redeploy_gate.fixtures.hello_world:
  native-capsule-receipt-invalid:...:receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
===== build outcome summary =====
OK=0  ERROR=1  CRASHED=0  TERMINATED=0
```

The load-bearing detail: **`expected-bytes` and `actual-bytes` are the same
number, 1648.** A receipt-content comparison is rejecting two payloads of
identical length, so this is a content/ordering/encoding difference, not a
truncated or short write — and the error text as written ("content-mismatch"
followed by two equal byte counts) gives an operator nothing to act on. The
message should carry the first differing offset and the two bytes there.

The surrounding harness behaved correctly and is not at fault:
`PASS — 1 check(s), stage stage2 failed (exit 2) and said why`.

## The SEGV did not reproduce

`doc/03_plan/infra/macos_open_bugs_fix_lanes_round2_2026-09-12.md` carries
"Stage 2 `serialize_mir_function` SEGV" as OPEN/unverified since 09-06, with
the instruction to reproduce or retire it. This run is the reproduction attempt:

- Stage 2's native build **completed**; the failure is in the sanity step after it.
- The failing unit exited **rc=1**, not 139/134.
- The build summary reports `CRASHED=0 TERMINATED=0`.
- No `serialize_mir_function`, `Segmentation fault` or `SIGSEGV` string appears
  anywhere under `.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/`.

So on this host, at this commit, Stage 2 does not SEGV. Retiring the SEGV item
outright is not justified from one run (it may be input- or cache-state
dependent), but it should be re-classed from "the remaining Stage-2 blocker" to
"not observed 2026-09-12; blocked behind two other defects", and the capsule
receipt mismatch above is what a Stage-2 lane should work on next.

## Note on where the artifacts landed

The lane was asked to keep artifacts under `build/bootstrap-r2/`. The bootstrap
script writes its own output root and ignored that: everything is under
`.simple/storage/build/bootstrap/`. Only the driver logs
(`build/bootstrap-r2/*.log`) and the launch wrapper are in the requested place.
The `[native-incremental] N reused / M rebuilt` receipt is NOT in the driver
log; it belongs in `.simple/storage/build/bootstrap/logs/<triple>/stage2-native-build.log`
and was absent from this run's copy of it.

## Seed reuse measurement (lane-1 item 4)

The 18m35s cold Rust seed floor is reducible without any new cache: the
digest-keyed store already exists as
`src/compiler_rust/target/bootstrap.generations/<digest>`, it is simply inside
a per-worktree cargo target dir. `cp -Rc` of an existing checkout's
`src/compiler_rust/target` into a fresh worktree (APFS clone, seconds, no extra
space) took the seed build to ~11 min on the first run, and a second run in the
same worktree reused it in **35 s**. No new script is needed; what is missing is
a documented shared-target path. Do NOT symlink the target dir.
