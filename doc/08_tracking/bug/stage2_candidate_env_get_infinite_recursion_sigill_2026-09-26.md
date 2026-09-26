# Stage 2 candidate sanity SIGILLs: `env_get` recurses into itself via duplicate co-compiled definitions

- **Filed:** 2026-09-26
- **Status:** PARTIALLY FIXED 2026-09-26 — the io_runtime cycle is fixed and landed, but Stage 2 admission is STILL RED; see "Post-fix state" at the end. The root cause is
  NOT duplicate `env_get` dispatch; the sections below are kept as the
  investigation trail and are corrected there.
- **Area:** cross-module symbol resolution / co-compiled duplicate dispatch
  (interpreter + JIT), `std.env`
- **Host:** yoon-note, x86_64-unknown-linux-gnu
- **Tree:** clean `origin/main` @ `c7e695bcff0` (NOT a stale-tree artifact — see below)

## Symptom

`sh scripts/bootstrap/run-phase1-local.shs --jobs=4` builds the Rust seed, clears
preflight, compiles Stage 2, then aborts at Stage 2 admission:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

`rc=132` is SIGILL. Reproduced directly against the stage-2 lane's own binary:

```
C=.simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple
SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_FREEZE_FALLBACK=1 \
  "./$C" native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o /tmp/cand.bin
# -> Illegal instruction, rc=132
```

## Root cause: `env_get` calls itself

The run prints its own cause before dying:

```
error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'env_get'
```

and, in the same log, the dispatch warning that explains why:

```
public function `env_get` has 4 co-compiled definitions with 2 differing signatures
  ((text)->Optional(text) vs (text)->text)
public function `env_get` has 6 co-compiled definitions with 2 differing signatures
  ((text)->Optional(text) vs (text)->text)
```

The warning text states the failure mode explicitly: *"JIT call sites resolve by
exact arg-type match (mangled `$dupN` variants), falling back to the last
definition when types are ambiguous — a fallback hit may still dispatch to the
wrong one."* Here the wrong one is **itself**: the `(text) -> text` wrapper's
internal call to the `(text) -> Optional(text)` overload resolves back to the
wrapper, so `env_get` recurses until the 1000-frame limit and the process traps.

The same log carries **72** distinct `co-compiled definitions with N differing
signatures` warnings (`_sha256_k`, `dir_create`, `file_read_text`, `join`,
`spawn`, `shell`, `process_wait`, …), so `env_get` is the first one to be hit on
this path, not the only latent instance. Anything that resolves by
"last definition wins" is a live mis-dispatch risk.

## Why two distinct definitions of `env_get` are co-compiled at all

The two signatures are the typed `Optional`-returning accessor and a
`text`-returning convenience wrapper. They become *co-compiled duplicates* — not
one module importing the other — when the compile closure pulls in more than one
copy of the same logical module. The stage-2 lane compiles under a sandboxed
`HOME`/`SIMPLE_LIB` with an SCV snapshot root
(`build/scv_snapshots/scv_revision_v1_<sha>/…`, cf.
`doc/08_tracking/bug/simpleos_cm33_policy_symbols_mangled_2026-09-26.md` where the
same snapshot root leaked into mangled symbol names), which is the obvious
candidate for how one logical module reaches the closure twice. **This part is a
hypothesis, not established** — the duplicate *count* rising 4 -> 6 within a single
run is consistent with it but does not prove it.

## It is NOT tree staleness, and NOT the seed's own native-build defect

Two confounds were ruled out explicitly:

- **Stale tree:** first observed on a working copy 1770 commits behind. Re-run on
  a clean `git checkout --force origin/main` (`c7e695bcff0`) with all current
  fixes present: identical failure. So it reproduces on mainline.
- **The separate seed-side `native-build` SIGILL**
  (`doc/08_tracking/bug/native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md`,
  fixed) is a *different* defect with a different mechanism (`ud2` at codegen
  entry from an empty backend table). Proof they are distinct: with that fix in
  place the **seed** builds the very same fixture successfully, both positionally
  and with `--source/--entry`:
  ```
  seed native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o out   -> rc=0
  seed native-build --source <dir> --entry hw.spl -o out                               -> rc=0 (cranelift and llvm)
  ```
  Only the stage-2 lane's binary traps, and it traps with a stack overflow in
  `env_get`, never with `ud2`.

## Unblock condition

`"./$C" native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o /tmp/x`
exits 0 for the stage-2 candidate, and `run-phase1-local.shs --stop-after-stage2`
reaches an admitted Stage 2.

Suggested order of attack:

1. Establish *why* `std.env` is co-compiled twice on this path — dump the compile
   closure for the stage-2 invocation and look for one logical module present
   under two paths (repo path vs SCV snapshot path is the prime suspect). Fixing
   the duplication removes the ambiguity at its source and would clear many of
   the other 71 warnings too.
2. Independently, make ambiguous duplicate dispatch **fail closed** instead of
   "falling back to the last definition". A self-recursive resolution is never
   correct, and today it is reported only as a warning; a hard error at resolution
   time would have named this in one line instead of a SIGILL 1000 frames later.
3. Do **not** paper over it by raising the 1000-frame recursion limit — the
   recursion is unbounded, so a larger limit only delays the trap.

## Related

- `doc/08_tracking/bug/native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md`
  — the seed-side native-build SIGILL (fixed); its still-open follow-up is that the
  parent's failure relay can itself report SIGILL instead of the worker's message,
  which is worth keeping in mind when reading `rc=132` from any bootstrap lane.
- `doc/08_tracking/bug/simpleos_cm33_policy_symbols_mangled_2026-09-26.md` — same
  SCV snapshot root leaking into symbol identity, fixed there for
  `__module_init_*`.
- Stage 2 is under active repair (60 stage2-related commits on `main` in the three
  days before this record); re-check against a newer `main` before investing.

## Resolution (2026-09-26)

**Real cause: a source-level infinite recursion in
`src/lib/nogc_sync_mut/io_runtime.spl`, introduced the same day by
`dac914d9306` ("real process exit codes on Windows").** That commit added
`if host_os() == "windows": return process_run_bounded(...)` to
`_io_runtime_process_run_raw` (`:36`). On every non-Windows host `host_os()`
(`:618`) shells out through `shell_output("uname -s")` (`:158`), which runs
through `_io_runtime_process_run_raw`, which asks `host_os()` again:

```
host_os -> shell_output -> _io_runtime_process_run_raw -> host_os -> ...
```

Established with the seed's dispatch probes (`SIMPLE_DEBUG_DUPDISPATCH=1`):
the 4-frame cycle repeats verbatim up to the trap, and **every hop is a
`P4-overload` resolution inside `io_runtime.spl` to the correct function**.
The trapped frame is whichever one lands on depth 1000 — `env_get` in the
worker (it is the first call inside `host_os`), `host_os` in a bare spec run.
`env_get` never called itself.

- **Hypothesis (SCV snapshot path duplicating `std.env`) — REFUTED.** The
  worker's loaded closure (strace of the seed interpreting
  `src/app/cli/native_build_worker.spl`, 1030 `.spl` opens) contains exactly
  6 `env_get` definitions in 6 distinct repo files — `io_runtime.spl:372`,
  `io/env_ops.spl:48`, `compiler/00.common/config.spl:13`,
  `nogc_async_mut/env/variables.spl:31`, `sffi/system_env_core.spl:9`,
  `nogc_sync_mut/env/variables.spl:28` — none under a snapshot root
  (`build/scv_snapshots/` does not exist; `SCV-W-FREEZE-FALLBACK` scans the
  working tree). The 4 -> 6 count is parent closure (`native_build_main.spl`)
  vs worker closure, not growth within one closure.
- **Duplicate-signature warnings are unrelated:** 42 warning lines / 31
  distinct names before the fix, 36 lines / the byte-identical 31 names
  after. They are real cross-module collisions but not this defect.
- **"Fail closed on self-binding dispatch" (item 2 above) is moot for this
  defect:** no resolution bound a call to its containing function, so no such
  check could have fired. The alias/facade shape of that trap is already
  refused in the seed (`interpreter_call/mod.rs:278`, hop back to the calling
  module).
- **Not stage-2-specific:** the older seed `bin/simple` traps identically under
  `SIMPLE_BOOTSTRAP=1`; without it `native-build` never interprets `io_runtime`.

**Fix:** `_io_runtime_process_run_raw` uses the compiled-in `platform_name()`
(`rt_platform_name`, returns `"windows"` on Windows, no process spawn) instead
of `host_os()`. `process_run_bounded` (process_ops) does not route back into
io_runtime, so the Windows branch is cycle-free too.

**Verification:** the reproducer above exits 0 and the produced binary prints
`hello`; both specs below fail on the unfixed tree with
`stack overflow: recursion depth 1000 exceeded limit 1000 in function 'host_os'`
and pass after.

## Specs

- `test/01_unit/lib/io_runtime/shell_output_host_os_no_recursion_spec.spl` —
  reproducing: `shell_output("uname -s")` and `host_os()` terminate.
- `test/01_unit/lib/io_runtime/process_run_raw_no_reentry_spec.spl` —
  generalization: the primitive's body references no spawning helper
  (`host_os(`/`shell_output(`/`shell_exec(`), `process_run` through it returns a
  real exit code, `platform_name()` is the spawn-free detector.

## Post-fix state (2026-09-26, later the same day) — Stage 2 admission is STILL RED

The `io_runtime` cycle fix above is real and landed, and it fixed the *standalone*
reproducer. It did **not** clear Stage 2 admission. Recording this so the FIXED
status above is not misread as "Stage 2 works".

What is true after the fix:

- Standalone, the stage-2 candidate now builds the fixture: `rc=132 -> rc=0`, and
  the produced binary prints `hello`.
- `run-phase1-local.shs --jobs=4` still aborts with
  `candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)`.
- This is **not** the stale-object-cache trap. The 160 MB
  `stage3/<triple>/stage2-native-cache` was deleted and Stage 2 rebuilt cold;
  the probe still returns 132.
- No `host_os()` call sites remain in `io_runtime.spl` (only its own definition
  and comments), and `platform_name()` delegates to `platform_name_raw()`
  (`rt_platform_name`, no spawn), so the documented cycle is genuinely gone.

The discriminating fact:

| invocation of the SAME candidate binary | result |
|---|---|
| `SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_FREEZE_FALLBACK=1 ... native-build <fixture>` | **rc=0**, prints `hello` |
| `SIMPLE_BOOTSTRAP=1 ... native-build <fixture>` (no SCV fallback) | rc=1, clean `SCV freeze has no admitted source inventory` |
| the stage-2 sanity probe's own sandboxed invocation | **rc=132** |

So the failure is specific to the probe's environment, not to the binary and not
to the command. The probe sanitizes the environment (`bootstrap-from-scratch.sh`
~`:1885-1893` resets `HOME`/`TMPDIR`/`PATH`, sets `LC_ALL=C`/`LANG=C`, and unsets
a list of `SIMPLE_*` vars) and runs the child via `setsid` under a 180 s bounded
wrapper. **Which specific variable flips the outcome has NOT been identified** —
that is the open question, and it is the next thing to bisect.

Evidence quality note: the probe's own captured log
(`stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`, 1354 bytes)
ends mid-`phase=parse` with **no diagnostic at all**, and its bounded-env sidecar
records only `reason=child-signal raw_status=132`. The readable `stack overflow
... in function 'env_get'` text came from the worker's SPILLED stderr
(`/tmp/native-build-stderr-<pid>-N.log`), not from the probe log. That is the
still-open parent-relay defect in
`native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md` (defect 3)
actively costing diagnosis here: the probe loses the child's message. Fixing that
relay should be done BEFORE further bisection, because right now every stage-2
failure is reported as a bare signal.

Revised unblock condition: bisect the sanity probe's sanitized environment against
a working standalone invocation of the same binary, one variable at a time, and
name the variable that turns rc=0 into rc=132. Do not assume it is SCV-related —
removing `SIMPLE_SCV_FREEZE_FALLBACK` produces a clean rc=1, never 132.
