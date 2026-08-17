# native-build worker: JIT vs interpret measurement (2026-07-30)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Assignment: measure the `native_build_worker.spl` compile pipeline under
`SIMPLE_EXECUTION_MODE=jit` versus the forced-`interpret` default, since
three independent lanes have now converged on "6+ minutes CPU-bound in
`parse_module_body`→`desugar_collections` for ONE file" as plausibly the
campaign's biggest single cost, and `run_native_build_worker`'s forced
interpret mode is overridable from the environment
(`native_build_main.spl:219-221`).

Load labeling (per instruction, machine shared with other sessions):
`uptime` immediately before the interpret run: `load average: 18.58,
17.03, 23.64`; immediately before the JIT run: `load average: 21.17,
20.43, 23.57`. Comparable, moderately loaded in both cases.

CPU-poller daemon (`kill_simple_monitor.shs`) confirmed live via `pgrep`
before starting — noted, not touched.

## Step 3 first (why is the default interpret?) — INFERRED, not proved

`git blame` on `native_build_main.spl:217-221` traces the forced-interpret
logic to commit `72319f47bf4a` ("fix: route native build main directly",
2026-07-06). The commit message and diff give **no explanation** for
*why* interpret specifically — the diff is a mechanical refactor
(extracting `run_native_build_worker`, adding
`native_build_should_use_worker`) with no comment at the forcing site.

Searched for an accompanying bug doc or commit explaining a specific JIT
defect being dodged:
- `doc/08_tracking/bug/cranelift_u8_array_literal_data_pointer_garbage_2026-07-06.md`
  is dated the same day, but is about cranelift-as-**freestanding-target-
  codegen-backend** (SimpleOS ring-3 `[u8]` array-literal data pointers)
  — a different layer from the **host-side JIT compilation of the worker
  tool itself**. Same-day coincidence, not a clear match.
- `git log --grep` across the full history for native-build+interpret/JIT
  rationale found no dedicated explanatory commit; the closest
  circumstantial evidence is a family of `fix(interp): register rt_*
  extern — native-build outage` commits, consistent with interpret
  already being the actively-maintained, battle-tested path by the time
  the worker-wrapping pattern was introduced, rather than a deliberate,
  documented dodge of one named defect.

**Verdict: INFERRED, unresolved** — no explicit "we chose interpret to
avoid JIT bug X" statement was found in this repo's history. This
pass's own measurement (below), however, is now **direct, concrete
evidence that interpret remains justified today**, independent of
whatever the original 2026-07-06 reasoning was.

## Step 1: the timed comparison

Both runs used the identical tiny-fn-main entry
(`src/os/crypto/_archive_entry_wots.spl`, importing `base_2b` and
`wots_msg_to_digits_128s` from the freshly-retyped `slh_dsa_wots.spl` —
same retype as passes 11/13/14/16) and the identical workspace-covering
invocation (`--source src/app --source src/lib --source src/compiler
--source src/os --entry-closure --emit-archive --no-mangle
--cache-dir <fresh, per-variant> --entry
src/os/crypto/_archive_entry_wots.spl`), invoking
`native_build_worker.spl` directly (bypassing `native_build_main.spl`'s
output-buffering wrapper, per the pass-16 technique) so progress streams
live. Both capped at `timeout 240` (240s); both hit the cap without
producing an output archive.

### Interpret baseline

`SIMPLE_EXECUTION_MODE=interpret` (explicit, matching the forced
default), `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`.

- **Wall clock**: 221s (measured `date +%s` before/after; capped by
  `timeout 240`, did not complete).
- **CPU time**: ~16,156 centiseconds (~161.6s) of `utime` accumulated by
  the last poll before the cap — i.e. **~73% of one core**, continuously,
  the whole run (consistent with a single-threaded, CPU-bound
  interpreter, not I/O-blocked).
- **Where it spent time**: closure discovery found exactly **one**
  import (`os.crypto.slh_dsa_wots -> src/os/crypto/slh_dsa_wots.spl`,
  confirming the crypto module's transitive footprint is trivially
  small, as established in pass 16) within the first ~10s of actual
  logic (after an initial ~2-2.5 minute silent interpreter-bootstrap
  phase loading the worker's own `compiler.driver`-touching module
  graph, per the pass-15 finding). After that single closure import, the
  log **never advanced again** for the remaining ~180s+ of the run —
  stuck in the per-file compile pipeline for that one file, matching
  pass 16's finding exactly (reproduced independently in this pass).
- **No JIT-fallback messages** (none expected — this run never invokes
  the JIT).

### JIT comparison

`SIMPLE_EXECUTION_MODE=jit`, `SIMPLE_JIT_STRICT=1`,
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`.

- **Wall clock**: capped at 240s, did not complete (process gone by the
  next poll after the last observed log growth, consistent with hitting
  either the `timeout 240` or a downstream cap — not distinguished
  further given the time budget).
- **CPU time**: 9,799 centiseconds (~98s) of `utime` at the last poll
  before the fallback-triggering error appeared (~200s wall-clock in,
  consistent with paying a similar or larger up-front cost before
  reaching the crypto module).
- **PROVED, the headline result — JIT does not merely run slower, it
  breaks**, exactly as predicted:
  ```
  [INFO] JIT compilation failed, falling back to interpreter: HIR lowering
  error: Unknown variable: bootstrap_hir_type_from_tag while lowering
  HirLowering.bootstrap_hir_type_from_tag
  ```
  `bootstrap_hir_type_from_tag` is a real, existing function —
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1779`,
  a **nested/local function** (4-space-indented, declared inside an
  outer function alongside a sibling nested `lower_domain_block` at line
  1775, not a top-level `fn`). This is part of the compiler's own
  HIR-lowering machinery — i.e. the JIT choked while trying to compile a
  piece of the **worker's own source code** (needed to run the worker at
  all), not the crypto target being built.
  - **`SIMPLE_JIT_STRICT=1` did NOT catch this** — the message text has
    no `"SIMPLE_JIT_STRICT:"` tag, so the pass-13 fix (which only
    hard-fails the specific `first_unresolved_import`/NULL-jump
    "unresolved external symbol" class) does not apply here. This is a
    **different, untagged JIT-failure family** (an HIR-lowering
    "Unknown variable" error, plausibly a nested/local-function-name
    resolution gap under the JIT's HIR lowering — distinct from, but
    reminiscent of, the already-documented "JIT closure ABI does not
    tag-box lambda arguments" limitation in `codegen/jit.rs`). **A real
    gap in strict mode's current coverage**, worth noting alongside its
    three wins elsewhere today.
  - After the silent fallback, the run continued (now effectively
    running that portion under the interpreter) but **also never
    advanced past the same single closure-import log line** for the
    rest of its capped lifetime — i.e. once JIT hands off to interpret
    for this code, the run degrades into the identical bottleneck the
    pure-interpret baseline hit, on top of having already burned ~98s+
    attempting JIT first.
  - **No output archive produced**, same as the interpret baseline.

## Step 3 continued: does today's landing cover this defect?

Checked the two commits named in the brief:
- `7935e97173743da62c8bb4e32a02ae1671f0665e` ("fix(jit): preregister
  trait types before declarations") — touches
  `hir/lower/import_loader.rs` and `hir/lower/module_lowering/
  module_pass.rs` for **trait-type preregistration**, a different
  subject (trait declarations, not nested-function name resolution).
- `98f3f1b081a7caba20223ee327b321ab5c50ee24` ("fix(jit): align
  run_file_jit's memory-safety strictness with the canonical compile
  lane") — about **W1006 mutation-capability strictness** alignment
  across lanes, also unrelated.

**Neither covers the `bootstrap_hir_type_from_tag` nested-function
"Unknown variable" HIR-lowering gap found this pass.** It remains open
and unfixed.

## Step 5 (profiling which phase dominates) — not reached, time-bounded

Both runs stalled *before* producing enough log signal to distinguish
`parse_module_body` from `desugar_collections` time (the `ZZZTRACE`
markers seen in pass 16 did not appear in either of this pass's runs —
possibly gated behind a different/additional env var, or specific to a
different code path than the one this exact invocation shape hits; not
investigated further given the time budget). Skipped, as explicitly
marked optional in the brief.

## Verdict

**JIT does not win — it breaks, exactly as predicted, on a genuine
HIR-lowering defect in the compiler's own nested-function handling, not
merely "runs slower."** This is not a close call requiring a risk
tradeoff: JIT cannot currently complete this build at all, independent
of speed. **Recommendation: do not change the default.** The forced
`SIMPLE_EXECUTION_MODE=interpret` in `native_build_main.spl:219-221`
remains necessary today, for a concrete, now-directly-observed reason
(this pass's finding), regardless of whatever the original 2026-07-06
rationale was (which this pass could not recover from history).

This also **closes off the speculation that JIT would simply be faster
if only it were used** — it cannot currently be used at all for this
code path. The campaign's "6-CPU-hour"-class cost is real and, per this
pass and the settling experiment before it, is a genuine per-file
interpreted-compile performance problem, **not addressable by an
env-var flip**. Fixing it requires either (a) fixing the
`bootstrap_hir_type_from_tag`-class nested-function JIT gap (and
whatever other JIT gaps exist in the worker's own ~1300-line compile-
target module graph — this pass found one specific instance, not an
exhaustive survey) so JIT becomes viable for the worker itself, or (b) a
compile-artifact cache on the run path (named by a sibling lane this
session as currently absent), or (c) direct interpreter performance
work on `parse_module_body`/`desugar_collections` (not distinguished
which dominates this pass, per step 5 above).

Landed as measurement only, per instruction — no default changed, no
retype applied or landed this pass (the entry file used to drive this
measurement, `src/os/crypto/_archive_entry_wots.spl`, imports
`slh_dsa_wots.spl`'s functions as-is, still `list`-typed from `main` —
the `[i64]` retype from passes 11/13/14/16 was deliberately not
re-applied this pass since the measurement's subject is the worker's
own compile performance, not the retype's correctness; the entry file
itself was removed after this pass's runs, consistent with prior
passes' scratch-file discipline).
