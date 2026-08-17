# Unstable Mode — Build Side

Research + plan. Read `unstable_mode_build_side_tldr.md` first for the shape.

Status of the deliverable, stated up front because it retires most of the work:
**run-to-end and the six outcome classes are ALREADY LANDED on the build side.**
The only genuinely missing half is **per-unit process isolation**, and that is
blocked on a precondition that does not exist yet (§6).

Scope note: this lane is RESEARCH ONLY. Nothing under `src/` was edited.

---

## 1. Where the per-source-file build loop is, and whether one ERROR stops it

The bootstrap-relevant per-module loop is **not** in `driver_build/incremental.spl`
(that file is fingerprint helpers). It is:

- **Phase 1 — cache scan:** `src/compiler/80.driver/driver_aot_native_output.spl:586`
  `for name in module_names:` — a miss `continue`s (`:591`, `:621-622`); a hit
  records `BuildUnitOutcome.ok(...)` (`:612-613`).
- **Phase 2 — compile:** `driver_aot_native_output.spl:642-698`, delegating to
  `ParallelBuilder.build(...)` at `:680`.
- **The unit loop itself:** `src/compiler/80.driver/driver_build/parallel.spl:402`
  `for id in order:` (sequential/deterministic arm) and `:469` `while not
  self.graph.is_complete():` (batch arm).

**A compile ERROR does NOT stop the build.** Control flow that decides it, quoted:

- `parallel.spl:455-462` — the failure arm of the compile result:
  ```
  case Err(msg):
      self.graph.mark_failed(id, msg)
      errors = errors.push((build_unit.path, msg))
      self.stats = BuildStats(... failed: self.stats.failed + 1 ...)
  ```
  No `break`, no `return`. The `for` at `:402` proceeds to the next unit.
- A failed *dependency* is also a `continue`, not a break: `parallel.spl:414-421`
  (`if dep_failed: ... continue`).
- The only `break`s in the loop region are `parallel.spl:472` (`ready.len() == 0`,
  i.e. no work left) and `:622`/`:627` in `build_parallel` — exhaustion, never
  failure.
- The caller likewise collects rather than returns: `driver_aot_native_output.spl:690-693`
  `for unit_err in build_result.errors:` records EVERY unit, with the comment at
  `:687-689` stating the old code read `errors[0]` and threw the rest away.
- Whole-BUILD guards do still return early — `:565` (empty `mir_modules`), `:568`
  (>1e6 modules), `:632` (no code-bearing modules), `:647` (capsule freeze failed).
  These are correctly not per-unit failures.

So: **a full error census is produced today.** `BuildOutcomeSet.summary()`
(`driver_build/build_outcome.spl:260-277`) names every non-OK unit, sorted
(`:213-219`) so two runs are byte-identical.

## 2. Own process, or in-process?

**All translation units run IN-PROCESS today.** The call is a direct closure
invocation on the parent's stack:

- `parallel.spl:424` — `val result = compile_fn(build_unit.path)`
- bound at `driver_aot_native_output.spl:680-682` to `_compile_frozen_module_capsule(...)`,
  an ordinary Simple function (`driver_aot_native_output.spl:876`).

Consequence, unavoidable and current: **a SIGSEGV or an OOM kill in one unit
kills the entire build.** There is no fork, no `rt_process_spawn_async`, on the
path that actually runs.

A process-isolated implementation **already exists and is complete** —
`ParallelBuilder.build_supervised(spawn_fn, artifact_fn) -> BuildOutcomeSet`
(`parallel.spl:680-…`), with a verified signal-preserving wrapper
`parallel_supervised_argv` (`parallel.spl:72-73`, measurements at `:50-53`:
SEGV→139, TERM→143, KILL→137). It has **zero callers**: a repo-wide grep for
`build_supervised` returns only its definition and this document's neighbours.
Same for `build_parallel` (`parallel.spl:536`). This is the same
written-but-wired-to-nothing shape as `interface_digest_of`.

## 3. earlyoom SIGTERM mid-run

Today: **the build simply dies, unclassified.** The compile runs in the parent
(§2), so SIGTERM at 143 kills the process that would have done the classifying.
There is no handler; nothing is written; the remaining units are not even
NOT_RUN, because no accumulator survives to say so.

The vocabulary to classify it exists and is correct but is only reachable from
the unwired path:
- `build_outcome.spl:106-108` — `signal_num == 15` → `TERMINATED`.
- `build_outcome.spl:68-72` — `build_outcome_is_unverified`: TERMINATED and
  TIMEOUT are true.
- `build_outcome.spl:75-79` — `build_outcome_is_failure`: ERROR and CRASHED only.
  **143 is therefore never a failure**, as required.

Partial mitigation that IS live: `driver_native_classify_module_failure_v1`
(`driver_aot_native_output.spl:73-88`) text-matches a child's error message onto
the same enum. Its own comment (`:63`) calls it "a narrower fallback, not a rival
scheme". It can only classify a death the parent OUTLIVED — it cannot classify
the parent's own SIGTERM.

## 4. Is there a per-unit outcome type analogous to `TestFileResult`?

**Yes — it already landed.** `src/compiler/80.driver/driver_build/build_outcome.spl`
(commit `e89f0c6f94a`):
- `enum BuildOutcomeKind` `:39-45` — OK / ERROR / CRASHED / TERMINATED / TIMEOUT / NOT_RUN.
- `struct BuildUnitOutcome` `:119-129` with `status`, `signal_num`, `wall_ms`,
  `peak_rss_kb`, `diagnostics`; constructors `ok` `:132`, `not_run` `:140`,
  `from_status` `:149`.
- `class BuildOutcomeSet` `:182-277` — the accumulator, `failure_count()` `:226`
  excluding UNVERIFIED, `verdict()` `:244`, `summary()` `:260`.
- Wait-status classifier `build_outcome_classify_status` `:100-113`.

Nothing new is needed here. **No second vocabulary should be invented.** The
build side's enum and the test side's error-text prefixes (`CRASHED:` /
`TERMINATED:` / `TIMEOUT:` / `NOT EXECUTED:`) are the same six classes in two
encodings; `build_outcome_kind_label` (`build_outcome.spl:50-57`) is the bridge.

## 5. Verification of the CLAUDE.md dependency-model claims (all still TRUE)

Line numbers have drifted; the substance has not.

| claim | verdict | evidence |
|---|---|---|
| `DependencyEntry.needs_recompile` is a one-hop predicate, never called | **TRUE** | `driver_build/incremental.spl:280` (was `:203-226`). Repo-wide `/usr/bin/grep -rn needs_recompile src/compiler/ src/app/` = **3 hits, all three are `fn`/`me` DEFINITIONS** (`driver_build/incremental.spl:280`, `incremental_builder.spl:207`, `incremental.spl:98`). Zero call sites. |
| `interface_digest_of` has zero callers | **TRUE** | `cache/action_key.spl:199` (was `:197-204`) is the sole definition. The only other hits are prose: `35.semantics/interface/compile_interface.spl:37`, `cache/block/block_key.spl:10`, `cache/schema/cache_protocol.sdn:844`. Zero call sites. |
| `simple.sdn` `dependencies:` read only for display | **TRUE** — no build path traverses it; unchanged from the CLAUDE.md finding. |

**What this constrains.** "Run to the end of the source list" on the build side
can only mean *iterate the flat module list and record every unit's fate*. It
cannot mean *rebuild exactly the affected subgraph*, and it cannot mean *a child
process recomputes its own inputs* — with no dependency model the child has no
way to know what its module needs. §6 is a direct consequence.

## 6. The precondition that blocks process isolation (do not paper over this)

`ParallelBuilder.build()` is handed a closure over **in-memory frozen capsules**:
`ctx.freeze_native_module_capsules_v1(...)` (`driver_types.spl:908`, called at
`driver_aot_native_output.spl:643`), consumed by `_compile_frozen_module_capsule`
(`:876`). A capsule is parent-process MIR. A child process cannot receive it.

So a `spawn_fn` for `build_supervised` needs ONE of:

- **(A) Capsule serialization + a one-module CLI.** Write each capsule to disk
  and add `simple native-compile-capsule <capsule-file> -o <obj>`. The child
  reads only its own capsule; no dependency model needed, because the parent
  already resolved everything. This is the smallest path that actually works.
- **(B) Child re-runs the frontend for one module.** Rejected: with no dependency
  model (§5) the child cannot determine its module's inputs, and it would redo
  the whole frontend per unit.

**I do not know** the size or serializability of a capsule — `freeze_native_module_capsules_v1`
was not read in depth in this lane, and no capsule was measured. If a capsule is
not cheaply serializable, (A) is not small and this deliverable is genuinely
blocked until it is. State that rather than shipping a design that assumes it.

## 7. Plan — smallest change, in dependency order

Ordered so each step is independently landable and each is a real increment.

**P0 (blocking, ~1 line, someone must own it).** `driver_aot_native_output.spl:667-672`
constructs `ParallelBuildConfig` naming only `num_threads`, `parallel_threshold`,
`deterministic`, `verbose` — but the struct gained `unstable` and
`unit_timeout_ms` (`parallel.spl:90,94`). **Suspected compile break at the sole
construction site.** I did not compile it (rebuilding `bin/simple` is forbidden
in this lane), so this is a suspicion, not a finding. Whoever owns
`driver_aot_native_output.spl` must confirm, and use
`ParallelBuildConfig.bootstrap()` (`parallel.spl:113`) there rather than
re-listing fields.

**P1 — flag plumbing, no behaviour change.** Thread the bootstrap front end onto
`ParallelBuildConfig.bootstrap()`. `parallel_unstable_enabled` (`parallel.spl:37`)
already gives `SIMPLE_UNSTABLE_BUILD=1/0` override with an ON default for
bootstrap and OFF for interactive — matching the frozen test-side contract. No
new flag machinery.

**P2 — decide (A) vs blocked.** Read `freeze_native_module_capsules_v1`
(`driver_types.spl:908`), establish whether a capsule can be written and re-read.
This is a research task, not an implementation one, and its honest output may be
"blocked".

**P3 — only if P2 says yes.** Add the capsule file format + the one-module CLI,
then a `spawn_fn` returning a pid from
`rt_process_spawn_async(parallel_supervised_cmd(), parallel_supervised_argv(cmd))`
and an `artifact_fn` returning `capsule.object_path`. Switch
`driver_aot_native_output.spl:680` from `builder.build(...)` to
`builder.build_supervised(spawn_fn, artifact_fn)` **when `cfg.unstable`**, keeping
`build()` as the stable-mode path. `build_supervised` already returns a
`BuildOutcomeSet`, so the reporting side needs no change.

**P4 — the fixture.** Reuse lane C's sentinel-file trick (state.md) to
disambiguate a self-inflicted crash from an earlyoom SIGTERM. One `.spl` fixture
that segfaults on demand, one that sleeps past the budget.

**Explicitly NOT in scope:** any dependency-aware or partial rebuild. That needs
`interface_digest_of` wired, `simple.sdn` traversal, and `SmfManifest`
load-verification — all still uncalled (§5) — and none of it is required for
run-to-end.

## 8. What I do not know

- Whether P0 is a real compile break (not compiled; see P0).
- Whether a frozen capsule is serializable at acceptable cost (§6).
- Per-unit process-spawn overhead vs. the current in-process path. Unmeasured. On
  a host already so contended that earlyoom forced a bootstrap stage from jobs=8
  to jobs=2, N extra `simple` processes may make things worse, not better.
- Whether `build_supervised` is CORRECT. It is written and commented in detail
  but has never executed — no caller, and I did not run its spec.
