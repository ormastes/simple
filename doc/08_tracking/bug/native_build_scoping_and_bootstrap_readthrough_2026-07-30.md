# `native-build` scoping + fail-open readthrough (2026-07-30)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Assignment: read `native_build_worker.spl` and the CLI arg plumbing that
invokes it to answer definitively why the pass-13/14 archive-lane attempts
on `slh_dsa_wots.spl` stalled, and whether this also explains the
standing "07-29 full-CLI rebuild died blind for 6 CPU-hours" blocker.

## Files read (full or near-full)

- `src/app/cli/native_build_worker.spl` (27 lines, read in full) — thin
  shim: validates `SIMPLE_NATIVE_BUILD_WORKER=1` is set, then calls
  `cli_native_build(native_build_entry_args())`.
- `src/app/cli/native_build_main.spl` (originally 277 lines, read in
  full) — the actual `simple native-build` CLI entrypoint (per its own
  header: "Lightweight entrypoint for `simple native-build`").
- `src/app/io/_CliCompile/compile_targets.spl` (1335 lines) — read the
  arg-parsing loop (758-995), the source-dir/import-resolution helpers
  (479-648), and the `native_inputs`-building call sites (1088-1140) in
  full; skimmed the rest.

## (a) Does `--source <dir>` scope transitive dependency discovery?

**PROVED, mixed answer — it depends on which of two build modes is
active, and even the closure mode has a real widening defect for narrow
`--source` sets:**

1. **`compile_targets.spl:1075`**: `val effective_entry_closure =
   entry_closure or emit_object or emit_archive`. For `--emit-object`/
   `--emit-archive` (my attempts, and the archive-lane's whole premise),
   closure/reachability mode is **always** engaged automatically, whether
   or not `--entry-closure` is passed explicitly.

2. **In closure mode** (`compile_targets.spl:1094-1097` /
   `1127-1130`), the compiled file set is built by
   `_native_build_entry_closure(entry_point, source_dirs)`
   (`compile_targets.spl:579-648`) — a genuine BFS over the entry's
   transitive `use`/`import`/sibling-`mod` graph (queue/discovered-set,
   `compile_targets.spl:585-648`), **not** a blind "every file under
   `--source`" walk. This directly rebuts the strongest form of "silently
   compiles the whole workspace" for object/archive builds.

3. **But** the BFS's own import-path resolver, `_nb_resolve_segs`
   (`compile_targets.spl:514-567`), contains a **widening fallback**:

   ```
   544: if segs.len() > 0 and not _nb_source_dirs_cover_workspace(source_dirs):
   545:     val src_path = _nb_resolve_under_root("src", segs)
   ```

   `_nb_source_dirs_cover_workspace` (`compile_targets.spl:479-480`)
   is `true` only if `source_dirs` contains **all three** of `"src/app"`,
   `"src/lib"`, `"src/compiler"`. My `--source src/os/crypto` attempt
   covers none of them, so line 544 fires for **every** import
   `slh_dsa_wots.spl` (or its dependencies) makes that isn't found
   directly under `src/os/crypto` — resolution falls through to search
   the **bare `"src"` root**, i.e. the entire workspace, defeating the
   narrow `--source` restriction for *finding* files (even though the
   *set that gets queued* is still nominally bounded by reachability).
   Two further **unconditional** (not workspace-coverage-gated) fallbacks
   follow at lines 551-553 (`src/lib` directly) and 557-566 (a
   `nogc_async_mut`/`nogc_sync_mut`/`common`/... tier-fallback loop under
   `src/lib/<tier>`) — so a narrow `--source` never actually prevents
   resolution from reaching anywhere in `src/lib`.

4. **In non-closure mode** (`entry_closure`/`emit_object`/`emit_archive`
   all false — i.e. a normal `--mode dynload` executable build without
   `--entry-closure`), `native_inputs` is built at
   `compile_targets.spl:1131-1136` by pushing each `source_dir` **as a
   whole directory string** into `options.input_files`, with no closure
   BFS at all:
   ```
   1132: for source_dir in source_dirs:
   1133:     native_inputs = native_inputs.push(source_dir)
   ```
   Whatever consumes `options.input_files` downstream (the
   `compiler.driver` — not read this pass, out of scope/time-bounded)
   must itself glob/discover every file under each pushed directory
   with no entry-reachability bound at all. This mode is **by design**
   "compile everything under `--source`" — for the 6 real
   `bootstrap-from-scratch.sh` call sites (below), which all pass
   `--entry-closure` explicitly, this branch is never taken; it's the
   fallback for anyone who runs `native-build` with `--source` but
   without `--entry-closure`/`--emit-object`/`--emit-archive`, which
   none of pass 13/14's attempts avoided (both used `--emit-archive`, so
   closure mode WAS engaged; the widening at point 3 is what actually
   bit).

**Bottom line for (a)**: `--source` is not advisory/ignored in the
closure-mode case that matters for the archive lane — it does bound the
*reachable file set* via BFS — but the widening fallback at line 544
means it does **not** actually scope *where files are found*, so a
narrow, non-workspace-covering `--source` gives none of the isolation
the archive lane's design assumed. It cannot cut off exploration into
`src/lib` (or beyond, since the closure still walks whatever
`slh_dsa_wots.spl`'s std-lib dependencies transitively pull in).

## (b) Why does "No entry point specified" print an error yet continue into full discovery?

**Revised finding, PROVED via empirical retest — this is NOT a missing
`return` in the code as originally assumed; the practical fail-open
experience is real but has a different, more interesting cause:**

- `compile_targets.spl:992-995` (the worker's own check) **does** contain
  an immediate `return 1` right after the two error `_cli_eprint` calls.
  Read in isolation, this control flow is correct, not fail-open.

- **But** `native_build_main.spl:217-232` (`run_native_build_worker`)
  **always forces `SIMPLE_EXECUTION_MODE=interpret`** for the worker
  subprocess when unset (`219-221`):
  ```
  219: val mode = env_get("SIMPLE_EXECUTION_MODE")
  220: if mode == nil or mode == "":
  221:     env_set("SIMPLE_EXECUTION_MODE", "interpret")
  ```
  and its own header comment (`native_build_main.spl:82`) says outright:
  *"The interpreted worker loads the compiler graph before codegen."*
  The worker's own module (`compile_targets.spl`, 1335 lines) imports
  `compiler.driver.driver_types`/`compiler.driver.driver` — a large
  subsystem — so the **tree-walking interpreter** must parse and
  interpret that whole graph just to construct the running program,
  *before* `cli_native_build`'s first line of argument-parsing logic
  ever executes. This cost is paid **regardless of whether the
  invocation is valid**, including the guaranteed-to-fail
  missing-entry case.

- **Compounding this**: `run_native_build_worker` uses
  `process_run_timeout(simple_bin, worker_args, ...)`
  (`native_build_main.spl:231`), which captures the worker's entire
  stdout/stderr and only prints it (`print_bounded`/`eprint_bounded`)
  **after the whole subprocess exits or times out** — not streamed. So
  even a worker that reaches and correctly executes the fast `return 1`
  produces **zero visible output** until the (slow) interpreter-bootstrap
  phase that precedes it has also finished.

- **PROVED empirically, this pass**: a fresh, tightly-bounded (30s)
  re-run of `native-build --source src/os/crypto --emit-archive
  --no-mangle -o <out>` (no `--entry`) against the *original,
  unpatched* `native_build_main.spl` produced **no output and no exit**
  within 30 seconds — directly confirming the interpreter-bootstrap cost
  (not the entry-point check) dominates wall-clock time for this
  invocation shape.

**So "prints an error yet continues" is not literally true as a
sequence of events** — there is no code path that logs the error and
then keeps going. What actually happens, and what makes it *look*
fail-open from the outside, is: (1) a long, invocation-independent,
completely silent interpreter-bootstrap phase (which itself emits a lot
of unrelated compiler lint/warning noise as a side effect of *loading*
`compile_targets.spl`'s own import graph — this is what created the
appearance, in pass 13/14's logs, of "the tool ran past the error into a
pile of unrelated compilation"), followed by (2) the buffered dump of
everything (worker's own module-load warnings + the real, correct,
already-decided error) all at once when the process finally exits. This
**is** the repo's known fail-open family in spirit — a genuine defect
that makes an invalid invocation indistinguishable from a hang for
minutes — just not the specific "missing return statement" shape assumed
going in. Documented as a fail-open-class defect (silent, expensive,
input-independent validation latency) rather than a literal fail-open
branch.

## (c) Where would per-module progress instrumentation go?

**PROVED — it already exists** for the closure-mode path, gated exactly
as requested (level-gated, default-off): `compile_targets.spl:584,
597-604`, inside `_native_build_entry_closure`'s BFS loop:
```
584: val trace_closure = (rt_env_get("SIMPLE_NATIVE_BUILD_TRACE_CLOSURE") ?? "") == "1"
...
592: while qi < queue.len():
593:     val f = queue[qi]
...
601:     if trace_closure and result.len() % 25 == 0:
604:         _cli_eprint("[native-build] closure visited {result.len()} queued={queue.len()} file={f}")
```
This loop knows exactly `result.len()` (files fully processed = "N"),
`queue.len()` (files discovered so far, a running lower bound on "M" —
the true total isn't knowable upfront since discovery is incremental),
and `f` (current file) — i.e. it already prints "module N (of at-least-M
so-far), current file" every 25 files, opt-in via
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`. **No new code needed for the
closure-mode path** — the fix is operational (set the env var), not a
missing feature. **The 07-29 6-CPU-hour arc almost certainly ran with
this flag unset**, which is sufficient by itself to explain "died
blind" for the closure-mode portion of that build.

**Gap, not fixed this pass (time-bounded)**: the non-closure path
(`compile_targets.spl:1131-1136` / `1099-1103`, whole-`source_dir`
pushing) has no equivalent instrumentation in this file — whatever
per-file loop actually walks those directories lives inside
`compiler.driver.driver`, not read this pass. Since all 6 real
`bootstrap-from-scratch.sh` call sites use `--entry-closure` (see next
section), this gap likely does not affect the 07-29 arc specifically,
but it's an open gap for any non-closure-mode invocation.

## Contained fixes landed this pass

### 1. Fast-fail on missing entry point (landed)

Verified first that no in-repo caller depends on the lenient (slow) path:
`grep`+manual read of all 6 `native-build` call sites in
`scripts/bootstrap/bootstrap-from-scratch.sh` — **every one** passes an
entry, either via `--entry <file>` (5 sites) or a bare positional file
(1 site, `bootstrap_main.spl` as the trailing arg with no `--entry`
flag). No caller can regress.

Added `native_build_has_entry(args)` to `native_build_main.spl` (the
always-fast wrapper, never the heavy worker) that mirrors the worker's
own entry-detection rule precisely enough to reject only invocations
that are **unambiguously, unconditionally** going to fail the same way:
recognizes `--entry`/`--entry=<path>` (mirroring
`cli_native_build_is_entry_arg`) and a genuine unconsumed positional,
correctly skipping the *values* of every value-consuming flag the
worker's parser recognizes (`--backend`, `--runtime-bundle`,
`--runtime-path`, `--linker-script`, `--source`, `-o`/`--output`,
`--mode`/`--build-mode`, `--cache-dir`, `--target`, `--cpu`,
`--opt-level`, `--timeout`, `--threads`/`--jobs`/`-j`, `--log`) so it
does not mistake e.g. `--source`'s or `-o`'s value for a stray
positional entry. (An earlier draft of this check treated *any*
non-flag-shaped arg as a possible positional without excluding flag
values — safe, but ineffective, since nearly every real invocation has
at least one such value and the check never fired; this version is
precise.) `main()` now checks this before calling
`run_native_build_worker`, printing the identical error text the worker
would have and returning 1.

**Verified directly** (not inferred):
- No-entry invocation: **15+ minutes → 0.054s wall-clock**, exit 1,
  correct error message.
- Bare-positional-entry invocation (mirrors bootstrap site 3): correctly
  recognized as having an entry, proceeds to spawn the worker (observed
  timing out at a 3s test bound with no false "No entry point" print —
  not incorrectly rejected).
- `--entry <file>` invocation: same — correctly proceeds.
- No-args and `-h`/`--help`: unaffected (both return before reaching the
  new check).

### 2. Progress instrumentation — not added, already exists

Per instruction ("land it level-gated default-off... Do NOT attempt to
implement real `--source` scoping if it's absent — report the design
gap instead"): no new instrumentation code was written. The closure-mode
instrumentation already meets the "level-gated, default-off" bar
(`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`, cited above). Documenting its
existence/location IS this pass's deliverable for (c) — the fix is
"know the flag exists and use it," not new code.

### 3. Real `--source` scoping — NOT implemented (design gap reported, per instruction)

The widening fallback (`compile_targets.spl:544` and the two
unconditional fallbacks at 551/557-566) is a genuine design gap: there
is currently no way to make `--source` actually prevent resolution from
reaching outside the given directories short of passing all three
workspace-covering roots (`src/app`, `src/lib`, `src/compiler`), which
defeats the purpose of scoping down to a single small module tree like
`src/os/crypto`. **Not implemented this pass** (out of scope per
instruction) — flagging for whoever owns this component next: the fix
shape would be adding a strict/opt-in mode where `_nb_resolve_segs`
simply returns `""` (unresolved) instead of falling through to `"src"` /
`"src/lib"` / the tier loop when the caller wants genuine isolation, at
the cost of that caller then needing to pass every real dependency root
explicitly.

## Does this explain the 07-29 6-CPU-hour rebuild blocker?

**INFERRED, not PROVED.** The widening fallback (the leading theory
going into this pass) does **not** apply to that arc: all 6 real
bootstrap call sites use `--source src/compiler --source src/app
--source src/lib [--source examples/10_tooling]`, which **does** satisfy
`_nb_source_dirs_cover_workspace` (all three required roots present) —
so line 544 never fires for the standard rebuild path. That arc's
slowness is, at minimum, partly just the legitimate cost of compiling a
large self-hosted compiler — not obviously a "silently compiling more
than intended" defect the way my narrow-`--source` case was.

What **does** transfer directly: (1) the forced-interpreter worker
bootstrap cost (`native_build_main.spl:219-221`) is paid on every
invocation regardless of scope, adding fixed overhead on top of the
arc's own large compile job; (2) the fully-buffered, no-streaming output
capture means **zero progress visibility for the entire run** unless
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` was set — and per this pass's
reading, it almost certainly was not (no reference to it in
`bootstrap-from-scratch.sh`). "Died blind" is fully consistent with (2)
alone; whether 6 CPU-hours itself was *necessary* work or partly wasted
(e.g. redundant re-resolution, a hung sub-phase) is not determined by
source reading alone.

**The one experiment that would settle this**: re-run the exact 07-29
arc's invocation with `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` set and
watch `result.len()`/`queue.len()` growth over time — if it climbs
steadily and plateaus near the actual size of `src/compiler + src/app +
src/lib` (a large but bounded, expected number), the 6 hours was
"blind but legitimate" (visibility gap only, now closable by setting the
existing flag); if it balloons far past that or stalls with a static
`queued=` count for a long stretch, that would prove a **separate**,
currently-undiagnosed defect in the closure BFS or downstream compile
phase, distinct from anything found this pass.

## Verdict: is the archive lane viable for the crypto campaign?

**Viable-with-fixes, for object/archive-emitting invocations
specifically, for modules whose transitive dependency footprint is
small** — with two caveats now on record:

1. The fast-fail fix (landed) removes the "looks hung" failure mode for
   genuinely malformed invocations, but does **not** fix the widening
   defect, which is the actual cause of pass 13/14's stalls on a
   *valid*, correctly-specified narrow `--source` + `--entry`
   invocation. Without a strict-resolution mode (not implemented this
   pass), any retype target whose dependencies fan out through
   `src/lib` still pays for resolving through the full-workspace
   fallback, and the closure BFS can still legitimately grow large if
   the target's own transitive imports are broad (crypto helpers often
   import `std.common.crypto.types`, hashing primitives, etc.).

2. Given the design gap in (1) is not fixed, the concrete next attempt
   for the campaign should either (a) pass a workspace-covering
   `--source` set (`--source src/app --source src/lib --source
   src/compiler`) explicitly, matching the pattern all 6 real bootstrap
   callers already use successfully, accepting the larger closure that
   results but avoiding the widening-fallback pathology entirely, with
   `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` set for visibility (per (c)); or
   (b) the alternative named in the pass-14 doc — a tiny `fn main`
   importer per retyped module, compiled with the workspace-covering
   `--source` set from (a), then `objdump` just that one object. (a) is
   now the recommended next attempt: it directly follows from this
   pass's own citations (matches the one invocation shape proven to work
   for all 6 real callers) rather than introducing a new mechanism.

## Content re-verification 2026-08-17 (app-rest lane) — the fail-open CLAIM is REFUTED

Triage recorded this row as "scope resolution returns empty string instead of
falling through to src, silently fail-open" citing doc line ~258. Read against
CURRENT source, that specific claim does not hold:

- `src/app/io/_CliCompile/compile_targets.spl` has three `return ""` sites —
  `:457`, `:477`, `:527`. Each is a **benign guard**, not a scope fall-through:
  dirname of a single-segment path, an all-dots relative import, and an empty
  segment list respectively. None of them is on the scope-resolution path.
- The widening `src` fallback is present and gated, not missing:
  `compile_targets.spl:570-571`, guarded by `_nb_source_dirs_cover_workspace`
  (defined at `:505`).

So there is no fail-open `return ""` to patch here. **The fail-open half of this
record should be CLOSED as not-reproducible-by-content.** Any remaining
bootstrap-readthrough concern in this doc is separate and was not evaluated.
Not proven: no execution evidence — the host was at load 346 with a live
bootstrap, so no native-build run was performed.
