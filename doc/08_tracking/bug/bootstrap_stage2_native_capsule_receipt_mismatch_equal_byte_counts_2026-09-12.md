# Stage 2 sanity fails `native-capsule-receipt-invalid` with IDENTICAL byte counts (macOS, 2026-09-12)

Status: **ROOT-CAUSED 2026-09-12. Receipt sites worked around in PR #677; the
underlying codegen defect remains OPEN and is the real item here.**
**Supersedes the Stage-2 `serialize_mir_function` SEGV as lane 1's Stage-2
blocker** — see "The SEGV did not reproduce" below before scheduling any work
against that older item.

## Root cause: an `i64` struct field read through an optional binding returns a BOX

This record asked for the first differing offset and the two bytes there. That
was added (PR #670) and it answered the question on the first rerun:

```
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
  :first-diff-line=4:expected=53657758209:actual=53657761281
```

Line 4 is the object SIZE. Both values are tagged heap pointers --
`0xc7e406a01` and `0xc7e407601` -- for a **632-byte** object file, and they are
**3072 bytes apart in the SAME process**. Reading the `i64` field `.size` off
an optional-bound `FileFingerprint` --

```
val object_fp = FileFingerprint.from_file(object_path)
if val fp = object_fp:
    ... "{fp.size}" ...
```

-- yields a fresh BOX per read under Stage-2 native codegen. The receipt is
WRITTEN from one such read and VERIFIED by recomputing it, so the two could
never agree, while being the same LENGTH. That is the whole of the reported
symptom.

`.content_hash` through the identical binding looked correct, and that is why
this survived two rounds of investigation: a `text` field IS a pointer, so a
boxed read of it is indistinguishable from a correct one. Only the `i64` field
exposed the defect. This is the same family as the
`case Ok(source): source.content` misread recorded in
`stage2_capsule_source_mutated_and_unreportable_reason_2026-09-07.md`.

**Two earlier hypotheses, both disproved -- do not re-litigate them:**
- *Nondeterministic across worktrees/hosts (timestamp, absolute path, host
  triple spelling).* No. Line 4 is the only differing line, and the two values
  differ within one process.
- *A dual `rt_file_size` extern declaration (`-> usize?` in
  `src/lib/nogc_sync_mut/fs.spl` vs `-> i64` in six other modules) whose boxed
  spelling won.* Fixed in PR #670 -- correctly, since one extern symbol must not
  carry two incompatible signatures -- and the mismatch REPRODUCED unchanged
  afterwards. It was not this defect.

## What landed, and what did not

PR #677 removes every path from a struct field to the receipt: the writer and
the verifier call `rt_file_size(object_path)` directly through a file-local
`-> i64` extern, and the phase-3 materialise site reads its two values from
locals instead of building a `FileFingerprint` and reading it back. Both
runtime call sites fail closed on the -1 stat sentinel, which
`FileFingerprint.from_file` passes through unchecked.

**That is a workaround at three call sites, not a fix.** The codegen defect is
untouched and will misread any other scalar field read the same way. Whoever
takes it: the reproducer is a one-field probe -- build a struct with an `i64`
field, wrap it in an Optional, bind it with `if val`, and print the field under
Stage-2 native codegen; a pointer-shaped value means the defect is live.

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
