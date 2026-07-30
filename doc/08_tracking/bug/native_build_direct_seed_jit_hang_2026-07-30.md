# `native-build` invoked directly against the seed hangs under JIT; `SIMPLE_EXECUTION_MODE=interpret` terminates

**Status:** open, root-caused to an engine (JIT) not a source or config defect,
underlying codegen mechanism not traced (belongs to a42f's overload-dispatch
thread). Filed 2026-07-30, during a self-hosted-interpreter string-
interpolation fix pass whose own `native-build` verification build never
completed and triggered this separate investigation.

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

## The result

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

**PROVED** (direct observation, both directions): the engine, not the
source tree or invocation config, is the discriminator.

## Why the existing interpret guard didn't fire

`native_build_main.spl:217-221` (inside `run_native_build_worker`) sets
`SIMPLE_EXECUTION_MODE=interpret` when the variable is unset or empty:

```
val mode = env_get("SIMPLE_EXECUTION_MODE")
if mode == nil or mode == "":
    env_set("SIMPLE_EXECUTION_MODE", "interpret")
```

`run_native_build_worker` is **pure-Simple CLI dispatch**, reached only
when `native-build` is invoked through the pure-Simple
`bootstrap_main.spl`/`cli_native_build` layer. Invoking `native-build`
directly against the Rust seed binary (`./simple native-build ...`, as
every reproduction in this doc did) reaches the seed's own native
`native-build` subcommand implementation, which spawns
`simple run src/app/cli/native_build_worker.spl ...` as a child directly —
**bypassing `run_native_build_worker` and its guard entirely.**

Worth stating explicitly, since it caused six wasted reproduction attempts
before it was found: **`SIMPLE_EXECUTION_MODE` being unset in the invoking
shell is not the same as the guard having run.** The guard only fires on
one specific call path; direct seed invocation is a different path that
silently lands on whatever the engine default is (JIT, per this campaign's
existing "deployed `bin/simple run` defaults to JIT" finding).

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

## Six hypotheses tested and refuted with direct evidence, before the seventh confirmed

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
7. **JIT miscompile in the seed's own execution of the worker script
   (CONFIRMED).** See below.

## The confirmed mechanism (engine, not yet traced to a specific defect)

`SIMPLE_EXECUTION_MODE=interpret`, set explicitly (bypassing the need for
the CLI-dispatch guard by setting it directly in the environment), was
tested against two independent trees:

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
**both terminate under `interpret`, where six separate attempts under
default (JIT-reaching) execution never terminated once across 5-67 minutes
each.** This is the discriminator.

### Suspected mechanism, not traced

Not independently traced in this pass (time-boxed; the coordinator
explicitly asked for a report rather than a fix attempt this session), but
a concrete, already-proven candidate exists in the campaign's own findings
from the same day: **a42f found the JIT misreads a struct field on an
array element** — a two-line repro (an element-tagged struct in an array;
the field reads correctly under the interpreter and reads empty under
JIT). A `while i < node.count`-shaped loop (or any loop whose bound or
advance depends on a struct field read off an array element) would never
terminate if that read silently returns a wrong/empty value under JIT —
which reproduces every element of the signature above: 100% CPU on one
thread, zero I/O (spinning over already-read data), flat RSS (re-walking,
not accumulating), and — critically — **a defect present in the JIT
engine itself would affect the known-good baseline identically to current
`main`**, which is exactly the "control also fails" result that killed
the regression hypothesis.

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

## Mitigation, proposed but not applied

Make the `SIMPLE_EXECUTION_MODE=interpret` guard in
`run_native_build_worker` apply **regardless of invocation path** — e.g.
by moving the env-var-forcing logic (or an equivalent check) into the
seed's own native `native-build` subcommand implementation, so that
invoking `native-build` directly against the seed binary cannot silently
land on the JIT engine.

This is a deliberate speed-for-correctness tradeoff, stated plainly: it
would make *every* direct-seed `native-build` invocation pay the slower
interpret-mode cost (as `native_build_worker_jit_vs_interpret_measurement_
2026-07-30.md` already measured and recommended keeping, for the CLI-
dispatch path), in exchange for never silently hanging on the JIT hazard
documented here. Not applied this pass — proposed only, per instruction, so
the decision to trade speed for correctness globally is made deliberately
rather than as a side effect of this investigation.

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
