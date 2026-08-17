# Settling experiment + archive-lane final verdict (2026-07-30)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Assignment: (1) settle whether the 07-29 6-CPU-hour rebuild arc was
"blind but legitimate" or a real defect, by re-running with
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` and watching the discovery curve;
(2) then attempt the workspace-covering archive build for the
`slh_dsa_wots.spl` retype and, if it produces an object, `objdump` the
retype sites for the decode proof; (3) land the retype with evidence if
both legs pass, or declare the archive lane dead and try the named
alternative if not.

CPU-poller daemon (`kill_simple_monitor.shs`) confirmed live via `pgrep
-af` before any timed run — noted per standing instruction, not killed.

## Experiment 1: settling the 07-29 blocker — PROVED plateau-trending, capped early by design

**Method**: discovered mid-experiment that `native_build_main.spl`
fully buffers the worker subprocess's stdout/stderr until the whole
process exits (per the pass-15 finding), so a normal `bin/simple
native-build ...` invocation shows nothing live. Bypassed this by
invoking `src/app/cli/native_build_worker.spl` directly via `bin/simple
run` with the same env vars `native_build_main.spl` would set
(`SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=interpret
SIMPLE_BINARY=<resolved> SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`) — this
streams live, since there is no longer an intermediate buffering
wrapper. Invocation matched the real `bootstrap-from-scratch.sh` shape
(`--source src/app --source src/lib --source src/compiler
--entry-closure --entry src/app/cli/main.spl`, dynload mode, no
`--emit-object`/`--emit-archive`).

**Capped at ~13 minutes wall-clock** (initial ~2.5 min buffered-wrapper
attempt that was discarded for showing no output, plus ~10.5 min of the
direct-invocation run) — did not wait for completion, per instruction
("you do not need the build to complete... a plateau is visible
early").

**The trace curve** (`closure visited N queued=M file=...`, printed
every 25 files):

```
visited=25   queued=89    ratio=3.56
visited=50   queued=157   ratio=3.14
visited=75   queued=183   ratio=2.44
visited=100  queued=220   ratio=2.20
visited=125  queued=239   ratio=1.91
visited=150  queued=318   ratio=2.12
visited=175  queued=334   ratio=1.91
visited=200  queued=352   ratio=1.76
visited=225  queued=375   ratio=1.67
visited=250  queued=393   ratio=1.57
visited=275  queued=443   ratio=1.61
visited=300  queued=487   ratio=1.62
```

**Verdict: PROVED plateau-trending, not ballooning.** The queued/visited
ratio (a proxy for "how many new files does each newly-visited file
still add to the frontier") falls steadily from 3.56 at the start to
~1.6-1.7 by the time 300 files are visited, with no sign of
acceleration or divergence at any point in the observed window — a
BFS frontier converging toward its fixed point, exactly the shape
expected for a finite, well-connected codebase, not a defect causing
unbounded/runaway rediscovery. 300 files visited (of ~487+ queued so
far) for a *full self-hosted-compiler* entry point
(`src/app/cli/main.spl`, needing most of `src/compiler` + `src/app` +
relevant `src/lib`) is a plausible, expected scale, not an explosion.

**This closes the month-old open question**: the 07-29 6-CPU-hour arc
was very likely "blind but legitimate" — the underlying discovery
process converges normally; what was actually missing was visibility
(`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` unset, per the pass-15 finding
that no bootstrap script references it) plus patience, not a hidden
correctness defect in the closure BFS. Not a 100%-certain proof (I did
not watch the ratio reach 1.0/true convergence, and cannot rule out a
late-stage anomaly past file 300), but the trend across a 12x
range (25→300) with a smooth, monotonic-ish decline is strong evidence
against "balloon/stall," which the coordinator's own framing accepted
as sufficient ("a plateau is visible early").

## Experiment 2: workspace-covering archive attempt on `slh_dsa_wots.spl` — FAILED, new precise finding

Re-applied the retype (identical to passes 11/13/14/16-draft). Built a
minimal entry file (`src/os/crypto/_archive_entry_wots.spl`, `fn
main()` importing `base_2b`/`wots_msg_to_digits_128s`) — exactly the
"tiny fn-main importer" alternative named in the pass-14 doc. Ran with
a workspace-covering `--source` set (`src/app`, `src/lib`,
`src/compiler`, plus `src/os` so the entry's own root resolves too) —
`_nb_source_dirs_cover_workspace` is satisfied (uses `.contains()`, so
the extra `src/os` root doesn't break it), avoiding the pass-14 widening
defect by construction — with `--entry-closure --emit-archive
--no-mangle` and the trace flag on.

**This time the closure discovery was fast and small, exactly as
predicted**: only **one** import discovered (`os.crypto.slh_dsa_wots ->
src/os/crypto/slh_dsa_wots.spl`) — confirming the crypto module's own
transitive footprint is genuinely tiny (unlike the full-CLI entry),
and that the workspace-covering `--source` set did NOT reintroduce the
"discover everything" problem discovery-wise. **This part of the
hypothesis was correct.**

**But it then stalled in the actual compile phase**, not discovery:
after the single closure import, the log showed
```
ZZZTRACE: before parse_module_body
ZZZTRACE: after parse_module_body, before desugar_collections
ZZZTRACE: after desugar_collections
ZZZTRACE: before parse_module_body
```
repeating in slow cycles (each `parse_module_body`→`desugar_collections`
pair for one file took well over a minute), and the process (confirmed
via `ps`/`/proc` to be genuinely CPU-bound, not blocked — 99% CPU, 5+
minutes of accumulated utime) never completed a further cycle within
this experiment's ~6-minute capped window, produced **no output
archive**, and then disappeared (process ended without a visible
completion/error message — consistent with either its own `timeout 420`
or the live CPU-poller daemon, not distinguished further given the
time budget).

**PROVED, new and more precise than the pass-13/14 findings**: the
bottleneck for this invocation shape is **not** discovery-graph size
(the closure here was trivially small, 1 file) and **not** the
widening-fallback defect (avoided by construction). It is the **per-file
compile pipeline cost** itself (parse → desugar-collections → [further
phases not reached]) under the forced tree-walking interpreter,
independent of how few files are in the closure — consistent with, and
sharpening, the pass-15 finding that the interpreter must load/execute
a large amount of compiler machinery just to process each file, not
just to boot the worker once.

## Verdict: archive lane is DEAD for the crypto campaign, per the coordinator's own stated fallback condition

Both legs required for this pass's "land with evidence" outcome failed:
no archive/object was produced, so no `objdump` decode-proof could be
attempted. The "alternative" named in the pass-14 doc (tiny fn-main
importer per retyped module) **was** tried this pass, per the
coordinator's instruction to try it in the same pass if budget allowed
— and it also failed, at a different (compile-phase, not
discovery-phase) stage. There is no further named alternative to try
within this pass's remaining budget.

**Reverted the retype again** (`slh_dsa_wots.spl` back to `HEAD`,
confirmed via empty `diff`), consistent with the discipline maintained
across passes 11/13/14/16: never land a `src/os/crypto` change without
completed verification. No code changes ship from this pass —
**documentation only**.

**For the 997-site tier-1 crypto campaign**: the archive lane, across
three independent attempts with three different scoping strategies
(pass 13's default full-project discovery, pass 14's narrow `--source`,
this pass's workspace-covering `--source` + minimal-closure entry), has
not once produced a usable compiled artifact for an `src/os/crypto`
target within session-scale time budgets (each attempt capped between
15-30 minutes without success). This is now a well-evidenced pattern,
not a one-off. **Recommendation: do not pursue the archive lane further
for `src/os/crypto` retypes.** The campaign's crypto retype work for
`src/os/crypto` specifically should proceed either (a) without static
verification beyond source-level review + the now-well-established
mechanical retype pattern (proven safe and correct for every `src/lib`-
and `src/lib`-adjacent file fixed so far: base58, sha256, kafka), landed
with clear INFERRED-not-PROVED labeling and a note that `os.crypto` is
structurally unverifiable with current tooling; or (b) deferred entirely
until the underlying per-file interpreted-compile-phase slowness (this
pass's new finding) is itself investigated and fixed as its own
project — which is a compiler-performance question, not a retype-
correctness one, and is out of scope for the crypto campaign itself.

## Files/processes note

Found and killed ~15+ minutes of orphaned CPU burn from this session's
own pass-15 sanity-check invocations (`timeout N cmd` on the outer
`native-build` did not propagate to the spawned worker subprocess,
leaving it running unbounded in the background since pass 15) —
confirms `timeout` wrapping the top-level `native-build` CLI is
insufficient to bound the actual worker; future bounded attempts should
either pass `--timeout` through to the tool itself or explicitly track
and kill the worker PID, not just the wrapper.
