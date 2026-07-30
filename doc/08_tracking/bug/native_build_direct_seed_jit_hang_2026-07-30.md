# `native-build` invoked directly against the seed hangs under JIT; `SIMPLE_EXECUTION_MODE=interpret` terminates. Mechanism UNKNOWN — an earlier version of this doc asserted a wrong explanation; see the correction below.

**Status:** open. **Confirmed:** default-mode `native-build`, invoked directly
against the Rust seed binary, never terminates; `SIMPLE_EXECUTION_MODE=interpret`
terminates on two independent trees. **NOT confirmed:** why. An earlier
version of this doc claimed the interpret guard in `run_native_build_worker`
was bypassed on direct-seed invocation. That claim is **retracted** — see
"Correction" below — and the mechanism is open again. Filed 2026-07-30,
during a self-hosted-interpreter string-interpolation fix pass whose own
`native-build` verification build never completed and triggered this
separate investigation.

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
