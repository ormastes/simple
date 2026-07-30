# `slh_dsa_wots.spl` retype — scoped archive-lane attempt #2 (2026-07-30)

Assignment: execute the scoped follow-up to the pass-13 blocked archive-lane
attempt — use a scoped `native-build` invocation (avoiding the
whole-program dependency-discovery graph that hit an unrelated,
pre-existing MIR-lowering gap in pass 13) to produce real compiled object
code for the retyped `slh_dsa_wots.spl`, `objdump` the retype sites to
prove element reads now decode (UnboxInt-equivalent) vs the untyped-list
raw-word path, and run the in-repo KAT spec as the semantic check. Land
only if all three legs pass; revert and document precisely otherwise.

## Step 4 (done first, per instruction): CPU-poller daemon check

`pgrep -af 'kill_simple_monitor|resource.*monitor'` at the start of this
pass found the daemon **live** — multiple `sh scripts/resource/
kill_simple_monitor.shs` processes running (this is the daemon flagged in
standing campaign memory as "supposedly fixed at a6819dcc788"; it is
**not** fixed, or has respawned). Not killed — shared environment
infrastructure, documented per instruction, not touched. Not actually
triggered this pass since no `bin/simple test`/KAT run was reached (leg 1
never produced a build to test against).

## Retype applied then reverted

Identical to passes 11/13 (`base_2b`/`wots_checksum_digits_p`/
`wots_msg_to_digits_p`/128s wrappers, `: list` → `[i64]`). Applied at the
start of this pass, **reverted at the end** — see Verdict.

## Leg 1: scoped compile — BLOCKED, two distinct failure modes tried

**Attempt A**: `native-build --source src/os/crypto --emit-archive
--no-mangle -o out.a` (no `--entry`). Failed immediately and cleanly:
```
Error: No entry point specified for native-build backend
Usage: simple native-build --backend=llvm --entry <file.spl> -o <output> [--source <dir>]...
```
The tool then, surprisingly, **continued past this error** and proceeded
to compile a large swath of unrelated files (`src/compiler/**`,
`src/app/**`) — i.e. `--source` alone without `--entry` does not scope
the build; it falls through to the same full-default-project discovery
that failed in pass 13, and hit the same class of pre-existing,
unrelated MIR-lowering errors (`unresolved method call: to_u64`,
`unsupported MIR type kind: HirTypeKind::Infer`) before exiting 1.

**Attempt B**: added a minimal entry file *inside* `src/os/crypto`
itself (`src/os/crypto/_archive_entry_wots.spl`, importing `base_2b` and
`wots_msg_to_digits_128s` from `os.crypto.slh_dsa_wots`) and ran
`native-build --source src/os/crypto --entry
src/os/crypto/_archive_entry_wots.spl --emit-archive --no-mangle -o
out2.a`. This time **no error at all** — the worker process (confirmed
via `/proc/<pid>/stat` utime polling across many bounded checks) was
genuinely, continuously CPU-bound (utime climbing steadily and
essentially 1:1 with wall-clock time, i.e. ~100% of one core, the whole
way through — not stalled), but produced **no output file and no log
output beyond the very first compiler warning line** after **~15
minutes**, well past this attempt's own `timeout 900` (900s) budget and
far past the "~6s/module" figure cited in the assignment as a prior
observation for per-module archive builds. Stdout/stderr appear to be
fully buffered until process exit or a flush threshold, so no
intermediate progress was observable beyond the utime signal.

**Killed at ~15 minutes** (this was my own spawned process tree, not the
shared CPU-poller daemon — safe to stop, unlike step 4's daemon). This is
a genuine, reproducible **build-time wall**, not a quick error this time:
scoping `--source` to a single small directory and supplying a
same-directory `--entry` did **not** bound the build's actual work to
anything close to the target files' own size — either `native-build`'s
dependency discovery ignores `--source` scoping for transitive `use`
resolution (walking the full `std`/`lib` tree regardless, since
`slh_dsa_wots.spl`'s own dependencies reach outside `src/os/crypto`), or
the "~6s/module" prior figure describes a different invocation shape
(e.g. an already-warm `--cache-dir`, or a smaller/differently-structured
target module) than what was tried here.

**Not chased further this pass** (time-bounded, per the 30-min-class cap
spirit even though this specific run used a 900s sub-budget): the next
thing to try would be an explicit `--cache-dir` reused across attempts
(a cold cache was used both times) and/or instrumenting/checking whether
`native-build`'s discovery genuinely respects `--source` at all for
transitive imports — neither attempted here.

## Leg 2: objdump decode proof — NOT REACHED

No object/archive was produced by either leg-1 attempt, so there was
nothing to disassemble. Not attempted.

## Leg 3: KAT — NOT REACHED

Per the three-legs rule, not run: leg 1 (compile) must produce a usable
artifact before the KAT semantic check is meaningful as part of *this*
lane's validation (the KAT spec can and does run independently of
`native-build`, under the interpreter, but running it here without a
successful leg 1 would not advance the archive-lane's own validation
question). Not run this pass.

## Verdict

**Lane did not complete end-to-end this pass — leg 1 (scoped compile)
failed twice, by two different mechanisms**: (A) `--source` without
`--entry` silently falls through to full-project discovery and re-hits
pass 13's unrelated blocker; (B) `--source` + a same-directory `--entry`
avoids that specific error but does not bound build time to anything
tractable within this pass's budget (killed at ~15 min, no artifact, no
error — a different failure shape than pass 13, but still not a
completed build). Reverted the retype again, consistent with the
established pass-11/13 discipline of never landing a `src/os/crypto`
change without completed verification — `slh_dsa_wots.spl` remains
unfixed on `main`.

**This is now two independently-documented, differently-shaped attempts
at the archive lane (pass 13's whole-program MIR-lowering-gap failure,
and this pass's two scoped-invocation attempts) that have not reached a
working demonstration.** The lane's viability for the 997-site tier-1
crypto campaign is **not yet established** — recommend the next attempt
either (a) get a definitive answer on whether `--source` genuinely scopes
transitive dependency discovery (read `native_build_worker.spl`'s own
source rather than treating the CLI flags as a black box), or (b)
fall back to a different validation strategy entirely for `src/os/crypto`
(e.g. a from-scratch, hand-rolled minimal test harness that links only
the exact functions needed, bypassing `native-build`'s whole-project
model) rather than repeating variations on the same CLI invocation.
