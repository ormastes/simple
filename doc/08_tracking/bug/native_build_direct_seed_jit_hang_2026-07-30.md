# `native-build` invoked directly against the seed hangs under JIT; `SIMPLE_EXECUTION_MODE=interpret` terminates. Mechanism UNKNOWN — an earlier version of this doc asserted a wrong explanation; see the correction below.

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
explanations. **Confirmed:** default-mode `native-build`, invoked directly
against the Rust seed binary, never terminates; `SIMPLE_EXECUTION_MODE=interpret`
terminates on two independent trees. **NOT confirmed:** why. An earlier
version of this doc claimed the interpret guard in `run_native_build_worker`
was bypassed on direct-seed invocation — retracted (see "Correction"). A
follow-up instrumented run then confirmed the guard DOES fire and its
env var DOES propagate correctly to the spawned worker (verified via
`/proc/<pid>/environ` directly), yet the worker still hangs before its own
`main()` is ever entered — see "Decisive instrumentation run" at the end
of this doc. The mechanism is open at a layer earlier than either prior
candidate explanation. Filed 2026-07-30, during a self-hosted-interpreter
string-interpolation fix pass whose own `native-build` verification build
never completed and triggered this separate investigation.

See also `doc/08_tracking/bug/native_build_worker_jit_vs_interpret_measurement_2026-07-30.md`
(sibling finding, same day, independent angle: JIT vs interpret timing on a
*different*, much smaller entry point — crypto module, single-import
closure — capped at 240s. That pass saw JIT reach a `[INFO] JIT compilation
failed, falling back to interpreter: ... Unknown variable:
bootstrap_hir_type_from_tag` message and then stall in the same bottleneck
as its interpret baseline. This doc's runs, on a much larger entry point
(`bootstrap_main.spl`, 726+/11k-file source tree), never produced *any*
JIT-fallback message or other output at all across six attempts — consistent
with the same underlying JIT weakness, reached earlier/more severely on a
larger closure, but not proven to be the identical failure mode.

## Correction (2026-07-30, same day): the "guard bypassed" explanation is wrong

The first version of this doc claimed `run_native_build_worker`'s
`SIMPLE_EXECUTION_MODE=interpret` guard never runs for a direct-seed
`native-build` invocation — that direct invocation reaches the seed's own
native subcommand implementation instead, bypassing the guard entirely.
**That is false, and the evidence that killed it:**

- `native_build_main.spl:258`'s error text —
  `"error: native-build worker exited with code {code}."` /
  `"  interpreter: {simple_bin} (exit code {code})"` — is a byte-for-byte
  match to output actually captured from a direct-seed reproduction in this
  investigation. That line only executes **inside**
  `run_native_build_worker`, **after** its guard and its
  `process_run_timeout` spawn call. If that error text appears, the guard
  function ran.
- Tracing `main.rs`'s dispatch: `command_is_pure_simple_tool("native-build")`
  returns `true`; neither of the two Rust-handler escapes
  (`SIMPLE_NATIVE_BUILD_RUST=1`, or a `--target` cross-build flag) fires for
  the plain `--backend cranelift` invocations used throughout this doc. That
  routes to `dispatch_to_simple_app("src/app/cli/native_build_main.spl",
  ...)`, which is on the allowed app-path list and runs `native_build_main.spl`
  in-process. There is no separate "seed's own native `native-build`
  subcommand implementation" that bypasses this file for a plain
  `--backend cranelift` call — the earlier doc's central claim was
  unsupported.

**So: the guard function runs on direct-seed invocations.** The mechanism
by which default-mode invocations still end up hanging (apparently under
JIT) is genuinely unknown as of this writing. Two explanations remain live
and undistinguished:

1. **The guard runs and calls `env_set`, but the mutation doesn't reach the
   spawned worker.** `rt_process_spawn_async` (`interpreter_extern/
   system.rs`) uses plain `std::process::Command::new(&*cmd)` with no
   `.env_clear()` — the only environment manipulation present
   (`clear_simple_child_stack_env`) only removes `_SIMPLE_STACK_SET`, not
   `SIMPLE_EXECUTION_MODE`. The actual spawned command is
   `/bin/sh -c 'exec timeout ... "$simple_bin" run
   src/app/cli/native_build_worker.spl ...'`, and POSIX `exec` preserves
   the shell's environment across the replace. **On paper, this should
   propagate** — `env_set` earlier in the same process should be visible
   to `Command::new(...).spawn()`, which reads the live process environment
   at spawn time. Whether it actually does was not verified.
2. **A decision point upstream of the guard routes default-mode invocations
   down a different path that never reaches it.** The sibling
   `native_build_worker_jit_vs_interpret_measurement_2026-07-30.md` doc
   references a `native_build_should_use_worker` check; if some condition
   causes that decision (or an equivalent one) to skip the worker-spawn
   path entirely for a subset of invocations, the guard would never run for
   those, independent of the `:258` match observed on a *different* run.

**The decisive next step, not yet taken, that would settle this in one
short run:** instrument `run_native_build_worker` directly — a print
right after its `env_set("SIMPLE_EXECUTION_MODE", "interpret")` call
(confirming the guard fires and what it believes it set), plus one inside
the spawned `native_build_worker.spl` itself reading `SIMPLE_EXECUTION_MODE`
back (confirming what the child actually received). This does not require
reproducing the multi-minute hang — the guard and the spawn both happen in
the first few seconds of any run, hung or not. Costs minutes, not another
hang-timing cycle.

**Because the mechanism is unknown, the mitigation proposed at the end of
this doc (making the guard invocation-path-independent) is NOT safe to
apply yet** — it was designed against the now-retracted bypass explanation,
and applying it without knowing which of the two explanations above is real
risks fixing nothing (if explanation 1 is correct, duplicating the same
`env_set` call elsewhere doesn't help) or fixing the wrong layer (if
explanation 2 is correct, the real fix is at the decision point, not the
guard itself).

## The result (unchanged, stands independent of the mechanism question)

`native-build` invoked **directly against the Rust seed binary**
(`./simple native-build --source src/compiler --source src/app --source
src/lib --entry-closure --entry src/app/cli/bootstrap_main.spl --backend
cranelift -o ...`) **never terminates** under default execution mode:

- Six independent attempts, two worktrees (one at current `main` tip, one at
  the `9ea0b39962d` baseline a sibling lane had previously built successfully
  in ~98.5s / 726 files), ranging 5 to 67 minutes each, zero exits, zero
  output beyond ~10-11 static startup lines (compiler lint warnings emitted
  during the first file or two of discovery).
- `SIMPLE_EXECUTION_MODE=interpret`, set explicitly in the invoking shell,
  **terminates** on two independent trees: a mutated (de-symlinked) copy of
  the baseline tree (~5.5 min, real error) and the pristine, untouched
  baseline tree (~13 min, different real error). Both are genuine
  completions — the process exits, a diagnostic is printed — not further
  hangs.

**PROVED** (direct observation, both directions): execution mode is the
discriminator between hanging and terminating. **NOT proved:** the specific
mechanism by which the mode takes hold or fails to (see Correction above).

## The signature (for the next person to recognise this in minutes, not hours)

Every hung run showed, without exception:
- One thread at ~100% CPU (`ps`/`top` aggregate `%CPU` on the parent
  process can be misleading — the process is multi-threaded and the
  *thread-group leader* is often idle on a futex; break down by
  `/proc/<pid>/task/*/stat` and `/proc/<pid>/task/*/wchan` to find the
  actual busy thread).
- That thread's `wchan` is `0` (actively running in userspace, not
  blocked on any kernel wait) — rules out I/O-bound or lock-contended
  explanations.
- `utime` tracks wall-clock 1:1 (continuous, not intermittent CPU use).
- Zero `read_bytes`/`write_bytes` growth (no I/O after initial page-cache
  warm reads) and flat RSS (not accumulating — consistent with re-walking
  rather than building up new state).
- No new log output, ever, beyond the same ~10-11 startup lines,
  byte-identical across independent runs.
- `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` produces **zero** trace lines —
  `_native_build_entry_closure` (`compile_targets.spl:579`) `_cli_eprint`s
  *before its first loop iteration* (on reading the entry file), so this
  places the spin **upstream of the closure-discovery BFS entirely** —
  somewhere in CLI arg handling, entry-point resolution, or (per the
  eventual diagnosis) the seed's own module-loading of the worker
  script's transitive dependency closure, before `main()` runs.
- **The known-good baseline (`9ea0b39962d`, previously built successfully
  by a sibling lane in ~98.5s) spins identically.** This is the single
  most important observation in this signature: it is what kills every
  regression/bisection theory outright, since an A/B whose control also
  fails is void, not negative evidence.

## Six hypotheses tested and refuted with direct evidence, before the seventh (partially) confirmed

1. **Source regression in the tree.** Bisection space between the known-good
   baseline and current `main` was tiny (3 commits touching
   `src/compiler`/`src/app`). Built the baseline commit itself, fresh
   worktree, identical setup — it also spun (same thread/CPU/RSS/I-O
   signature). Refuted: the control failing voids the A/B before a single
   candidate commit was even tested in isolation.
2. **Runtime-path/symlink environment mismatch.** Replicated a sibling
   lane's exact documented setup (real, non-symlinked `target/` directory;
   `target/bootstrap` physically copied, not symlinked, 4.7GB; the same
   LLVM-linked seed binary; `--backend=cranelift` explicit). Still spun,
   same signature. The "`falling back to static`" runtime-provider warning
   present in every run turned out to be an unrelated, cosmetic warning
   about the seed's own dynamic SFFI loading wanting a file where a
   directory was given — not connected to the hang.
3. **Export-statement parse-error recovery loop.** The last log line before
   every hang (`Example: export use module.{A, B, C} or export A, B from
   module`) looked like it could be an error-recovery hint. Traced the Rust
   seed source directly: it's an `ErrorHintLevel::Warning` emitted *after*
   the `export use` statement already parsed successfully — a benign lint
   against glob exports, not an error, and not a recovery path. Confirmed
   two independent hung runs produced byte-identical logs ending on this
   exact line, proving it's deterministic early-discovery output, not a
   marker near the actual spin.
4. **`--source` argument widening fallback** (`compile_targets.spl:544`,
   `if segs.len() > 0 and not _nb_source_dirs_cover_workspace(source_dirs):
   ... resolve under bare "src"`). Traced the accumulation code directly:
   `--source` values are correctly `.push()`-appended per occurrence (no
   overwrite bug), `source_dirs` starts empty (not pre-seeded with
   `"src"`), and `_nb_source_dirs_cover_workspace` correctly recognizes the
   three canonical roots when all three are passed. This specific fallback
   is a per-import resolution fallback, not a wholesale re-scan, and
   doesn't fire for the exact invocation used throughout. Refuted for this
   invocation, though the underlying file-count discovery (`src/compiler` +
   `src/app` + `src/lib` = 11,183 `.spl` files on disk, 11,180 git-tracked
   at HEAD, 0 untracked — legitimate, not generated-file pollution) was a
   real and useful side-finding pointing toward hypothesis 5.
5. **Closure-discovery infinite loop.** `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`
   produced zero output across a 6+ minute run, and (per the signature
   section above) that function's own tracing fires before its first loop
   iteration — so the spin is provably upstream of this BFS, not inside it.
6. **Symlink aliasing / combinatorial closure blowup.** `src/compiler` has
   17 top-level symlinks (`backend -> 70.backend`, `frontend -> 10.frontend`,
   etc., all sibling directories within `src/compiler`, no cycles); `src/app`
   has 7 more, some cross-directory (`lsp -> ../lib/nogc_sync_mut/lsp`) and
   some pointing outside `src` entirely (`mcp_t32 -> ../../examples/...`).
   Hypothesis: if module/file discovery follows symlinks without
   canonicalizing paths before deduping, the same underlying files get
   discovered under multiple module-name spellings, and if downstream logic
   treats those as new work, the closure could blow up combinatorially.
   Tested empirically in two stages — replaced `src/compiler`'s 17 symlinks
   with real copies of their targets (same content, no aliasing), still
   spun with the identical signature; then extended to all symlinks under
   all three `--source` roots (0 symlinks remaining anywhere in the closure
   scope), still spun, identical signature. Cleanly refuted, in full, not
   partially.
7. **JIT is the discriminator (execution-mode result CONFIRMED); the
   "guard bypassed" explanation for WHY was asserted, then itself refuted
   (see Correction above).** The engine matters — that part stands. The
   causal chain from "default execution mode" to "the guard's effect not
   taking hold" is open.

## The confirmed result and the open mechanism, restated

`SIMPLE_EXECUTION_MODE=interpret`, set explicitly in the invoking shell
(sidestepping whatever the in-process mechanism is, by fixing the variable
before the process even starts), was tested against two independent trees:

- A de-symlinked (mutated, from hypothesis 6's test) tree: terminated in
  ~5.5 minutes with `error: native module name collision after path
  sanitization: 'src/compiler/10.frontend/core/parser_preprocessor.spl'
  and 'src/compiler/frontend/core/parser_preprocessor.spl' both map to
  'compiler.10.frontend.core.parser_preprocessor'` — a real, self-inflicted
  collision from the de-symlink test mutation (replacing the `frontend`
  symlink with a real copy created a genuine second file with the same
  sanitized module name), not present in the pristine tree, but notable as
  **the first run in the entire investigation that ever exited.**
- A pristine, untouched fresh worktree at the same baseline commit
  (symlinks intact, no mutation): terminated in ~13 minutes with
  `error: semantic: method 'len' not found on type 'str' (receiver value:
  <corrupted char>)` — a different, real, and separately-interesting error
  (see below), but again: **termination**, not a hang.

Two independent trees, two different real errors, one common property:
**both terminate under `interpret` set externally, where six separate
attempts under default execution never terminated once across 5-67 minutes
each.** This remains the strongest available evidence that execution mode
(not source, not config, not symlinks) is the discriminator. It does NOT
by itself prove *why* the in-process guard fails to achieve the same effect
— see Correction above for the two live, undistinguished explanations and
the one short instrumentation run that would settle it.

### Suspected downstream mechanism, not traced

Not independently traced in this pass, but a concrete, already-proven
candidate exists in the campaign's own findings from the same day: **a42f
found the JIT misreads a struct field on an array element** — a two-line
repro (an element-tagged struct in an array; the field reads correctly
under the interpreter and reads empty under JIT). A `while i < node.count`
-shaped loop (or any loop whose bound or advance depends on a struct field
read off an array element) would never terminate if that read silently
returns a wrong/empty value under JIT — which reproduces every element of
the signature above: 100% CPU on one thread, zero I/O (spinning over
already-read data), flat RSS (re-walking, not accumulating), and —
critically — a defect present in the JIT engine itself would affect the
known-good baseline identically to current `main`, which is exactly the
"control also fails" result that killed the regression hypothesis. This is
a candidate for what JIT does once it's reached (whatever the reason it's
reached under default mode); it is not itself evidence about why the
interpret guard's effect doesn't take hold.

**Important qualifier, from the same finding:** a42f's fix for the
*specific* two-line repro was a **source-level workaround, not a JIT
repair** — it renamed `BeDomNode`'s 2-arg `element` overload to
`element_with_id` to sidestep the underlying defect (two same-named
methods differing only in arity, in one impl block, silently corrupting
field reads under JIT dispatch). The underlying JIT dispatch defect **is
still live everywhere else in the tree** that has the same overload
shape. Whether the compiler's own native-build path (`compile_targets.spl`,
`module_lowering.spl`, or elsewhere in the ~726-11k file closure) contains
a same-name/different-arity static-method pair on an impl block is an open
question — a42f's repo-wide scanner is unreliable for this (cannot
distinguish impl-block methods from nested `extern fn` declarations), so a
narrow, hand-checked search restricted to the files this specific
native-build path actually traverses would be the tractable next step, not
attempted this pass.

## The separate `<corrupted char>` receiver error

The pristine-tree interpret-mode termination's error —
`error: semantic: method 'len' not found on type 'str' (receiver value:
<corrupted char>)` — is flagged but not chased. A `.len()` call reaching a
corrupted (non-UTF8 or otherwise garbage) `str` receiver is itself a real,
likely-separate defect from the JIT hang, surfaced only because interpret
mode got far enough to hit it. Worth a fresh, targeted investigation of its
own; not investigated further here given the session's time budget.

## Mitigation, proposed earlier — NOT safe to apply, pending the mechanism

An earlier version of this doc proposed making the
`SIMPLE_EXECUTION_MODE=interpret` guard in `run_native_build_worker` apply
regardless of invocation path. **That proposal presumed the now-retracted
"guard bypassed" explanation and is not safe to apply as designed.** Until
the decisive instrumentation run (see Correction above) distinguishes
between "the guard runs but `env_set` doesn't reach the child" and "a
decision point upstream skips the guard for some invocations," a fix
aimed at "apply the guard elsewhere" risks either duplicating an `env_set`
call that already runs and already doesn't work (explanation 1), or
missing the actual branch point entirely (explanation 2). Revisit once the
mechanism is confirmed.

## Reproduction commands (for whoever picks this up)

```
# Hangs (direct seed invocation, default/unset SIMPLE_EXECUTION_MODE):
./simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/cli/bootstrap_main.spl --backend cranelift \
  -o build/bootstrap/stage2/simple

# Terminates (same command, interpret forced explicitly):
SIMPLE_EXECUTION_MODE=interpret ./simple native-build --source src/compiler \
  --source src/app --source src/lib --entry-closure \
  --entry src/app/cli/bootstrap_main.spl --backend cranelift \
  -o build/bootstrap/stage2/simple
```

Diagnostic recipe for the "single busy thread" signature, when `gdb`/`perf`
are unavailable (`kernel.yama.ptrace_scope=1`,
`kernel.perf_event_paranoid=4` in this environment, both denied):

```
pgrep -af native_build_worker              # find the worker PID
for t in /proc/<pid>/task/*/; do
  tid=$(basename "$t")
  utime=$(awk '{print $14}' "$t/stat")
  wchan=$(cat "$t/wchan")
  echo "tid=$tid utime=$utime wchan=$wchan"
done
```
The busy thread has `wchan=0` and a `utime` that grows in lockstep with
successive samples' wall-clock gap.


## Decisive instrumentation run (2026-07-30) — the mechanism reopens, doesn't close

Per the "decisive next step" above, instrumented a fresh worktree (temporary,
local, not committed — given the hour, a level-gated permanent trace was not
worth the extra land/verify cycle for a one-shot diagnostic):

- `run_native_build_worker` (`native_build_main.spl`): a print immediately
  before the guard (`mode-before={mode}`) and one immediately after
  (`mode-after-guard={env_get("SIMPLE_EXECUTION_MODE")}`).
- `native_build_worker.spl`'s `main()`: a print as its literal first
  statement, before even the `SIMPLE_NATIVE_BUILD_WORKER` check, reading
  `SIMPLE_EXECUTION_MODE` back.

Ran the exact default-mode reproduction (`SIMPLE_EXECUTION_MODE` unset in
the shell, direct-seed `native-build` invocation).

**Result — outcome 1 of the three anticipated, the "surprising and
important" one:**

```
GUARD-PROBE: run_native_build_worker entered, mode-before=nil
GUARD-PROBE: mode-after-guard=interpret
```

Both printed within ~10 seconds, confirming (again, directly) that the
guard runs and its own `env_get`/`env_set` round-trip believes it succeeded.

The worker subprocess was then confirmed alive (`pgrep`) and its **actual
OS-level environment was read directly, bypassing the need for the worker's
own code to run at all**:

```
$ cat /proc/<worker-pid>/environ | tr '\0' '\n' | grep SIMPLE_EXECUTION_MODE
SIMPLE_EXECUTION_MODE=interpret
```

**The environment variable does propagate correctly to the child.** This
directly refutes explanation 1 from the Correction above ("`env_set`
doesn't reach the spawned worker") — it does reach it, confirmed at the
OS level, not inferred.

And yet: **`WORKER-PROBE` — the literal first statement of the worker's
`main()` — never printed**, across more than 4.5 minutes of the worker
process showing the exact same signature documented throughout this doc
(one thread pegged, `wchan=0`, `utime` tracking wall-clock 1:1, per
`/proc/<pid>/task/*/stat`). The worker hangs before its own `main()` is
ever entered — before argument parsing, before `cli_native_build`, before
anything this doc's earlier sections attributed the spin to. This is
consistent with, and sharpens, the standing "upstream of the closure BFS"
finding: the spin is not merely upstream of `_native_build_entry_closure`,
it is upstream of the worker's `main()` entirely — in the seed's own
loading/compilation of `native_build_worker.spl` and its transitive import
closure (most of `src/compiler`), which happens automatically before any
user code in the script runs.

**This reopens the diagnosis rather than closing it, exactly as
anticipated for this outcome.** The env var is confirmed correct in the
hanging child's own environment; the mechanism by which execution mode
still determines hang-vs-terminate is now open at a different, earlier
layer than either previously-proposed explanation named.

**One unreconciled tension, flagged rather than chased further:** this
run's child had `SIMPLE_EXECUTION_MODE=interpret` in its own environment
from spawn and still hung. But the two prior successful terminations
(the mutated tree at ~5.5 min, the pristine tree at ~13 min, both earlier
in this doc) were produced by setting `SIMPLE_EXECUTION_MODE=interpret`
directly in the invoking shell, before starting the *entire* process tree
— meaning in those runs the **parent** `native-build` process itself also
ran under interpret, not just the worker child. This run's parent ran
under default mode (JIT), with only the child's environment corrected via
the in-process guard. A plausible reconciling hypothesis — **the parent's
own execution mode matters too, independent of what the child's
environment says, possibly via a shared cache, lock file, or other
inherited state rather than the env var itself** — was not tested. That is
the natural next instrumentation run for whoever continues this, not
undertaken here per the "no fix, no further chase tonight" instruction.

**Status of the mitigation, restated:** still not safe to apply. The
env-propagation explanation it was implicitly compatible with is now
directly refuted. Any fix attempt needs to target the pre-`main()`
script-loading phase, a layer neither this doc's original mitigation nor
its two prior candidate explanations addressed.

## 2026-07-31 — the tool documents this condition itself

A cell run left to go long enough finally printed the parent's own
diagnostic, which no earlier attempt had ever seen:

```
error: native-build worker timed out after 7200s before producing a binary.
  The interpreted worker loads the whole compiler + LLVM import graph before any
  codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget. Raise
  --timeout, shrink --source, or use the in-process backend for cross-target builds.
```

**Honest scope of this observation.** The "after 7200s" figure is NOT
literally true for the run that produced it: the worker was killed
manually at roughly 30 minutes and the parent emitted its standard
timeout message in response. So the trigger was the kill, not a genuine
budget expiry. What is load-bearing is the message TEXT, which is the
tool's own documentation of this failure mode.

**Why nobody saw it before.** Every prior attempt was killed well short
of the 7200s budget — the longest was 67 minutes (~4020s). The
diagnostic only prints when the worker's wait ends, so the explanation
was always one unbroken run away.

**What it says, and why it fits.** The interpreted worker loads the whole
compiler + LLVM import graph BEFORE any codegen, and a large `--source`
set exceeds the budget. Every cell in this investigation used exactly
such a set (`--source src/compiler --source src/app --source src/lib`).
This is consistent with the observations that killed the other theories:
the known-good baseline commit behaves the same because the load cost is
inherent to the source-set size, not to any commit; de-symlinking and
runtime-path changes do not move it because they do not change how much
gets loaded; and it stalls before the worker's `main()` because the
import graph loads first.

**Remedies the message itself names:** raise `--timeout`, shrink
`--source`, or use the in-process backend for cross-target builds.

**What still stands.** Execution mode remains a genuine discriminator:
the two interpret-mode runs recorded above terminated at ~5.5 and ~13
minutes with REAL errors (a native module-name collision after path
sanitization, and a `method 'len' not found on type 'str'` corrupted
receiver) — they failed on their own faults well before any budget was
reached, rather than running to the timeout.

**NOT VERIFIED.** No run in this investigation has been allowed to reach
7200s uninterrupted, so "the budget is genuinely the terminating
condition for the default-mode path" is inferred from the message text
and remains unproven. Confirming it requires one uninterrupted run to
completion, or a run with `--timeout` raised, or a shrunken `--source`
set that completes quickly. That is the cheapest decisive next step.

## 2026-07-31 — MEASURED: not a hang, and the diagnostic's mechanism is WRONG

The section above took the parent's error message at face value. A direct
measurement refutes its mechanism and the "hang" framing together.

**Method that finally worked:** run the worker DIRECTLY
(`native_build_worker.spl`, `SIMPLE_NATIVE_BUILD_WORKER=1`, `--timeout 3000`,
`stdbuf -oL -eL`, `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1 --verbose`) to get live
streaming output instead of the parent's exit-buffered capture.

**IT TERMINATES.** 1341s (~22.4 min), deterministically, with a real semantic
compile error (`method 'len' not found on type 'str'`) — not a timeout, not a
hang, and far under the 7200s budget.

**Breakdown:**
- ~18 of the 22 min is the `--entry-closure` BFS import-resolution walk
  (`_native_build_entry_closure`) crawling 484 files — about **2.2 s/file** for
  what is documented as a cheap, purely syntactic scan.
- Only then does `Driver start: inputs=484` fire; the driver parsed ~5 modules
  (~4 min) before hitting the semantic error.

**Three corrections to the message's own text:**
1. **"Loading the whole compiler + LLVM import graph" is NOT the slow part.** An
   import-graph-only probe (`use app.io._CliCompile.compile_targets.{cli_native_build}`
   with no build call) loaded that entire graph in **24 s**.
2. **`--entry-closure` DOES narrow the input set** — 484 files, not the
   multi-thousand-file tree. It works as designed.
3. **Raising `--timeout` does not yield a successful build.** A separate real
   semantic bug blocks success regardless of timeout or source-set size.

**WHY EIGHT INVESTIGATIONS CALLED IT A HANG — the root cause of the confusion.**
`native_build_main.spl`'s `process_run_timeout` **buffers the worker's stdout
until process exit**. An observer watching that stream sees nothing for 20+
minutes, so a slow-but-progressing run is **indistinguishable from a hang by
design**. Every prior attempt (5-67 min, "no completion") was almost certainly
this same ~22 min run killed early. The fix for the *observation* problem is to
run the worker directly with `stdbuf -oL -eL`, as above.

**Supersedes:** the "budget exceeded" reading in the section above. That section's
own NOT VERIFIED caveat was correct to doubt it — the budget was never the
terminating condition.

**Real defects this leaves, both worth their own work:**
- `_native_build_entry_closure` at ~2.2 s/file for a syntactic scan.
- The `method 'len' not found on type 'str'` semantic error at ~5 modules in.
