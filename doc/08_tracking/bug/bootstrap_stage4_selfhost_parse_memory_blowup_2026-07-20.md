# Stage-4 self-host full-CLI build: parse-phase memory blowup (~160MB/file, killed at 64GB)

- **ID:** bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** high (blocks the stage3-compiled stage-4 lane entirely; seed-compiled fallback lane unaffected)
- **Lane:** bootstrap `--full-bootstrap --mode=one-binary --backend=cranelift`, x86_64-linux

## Symptom
When the stage-3 self-hosted binary compiles the full CLI (stage 4, `main.spl`,
1777 files), RSS grows ~160MB per parsed file and reached **64GB at 403/1777
files** before the repo `kill_monitor` terminated it. Extrapolated requirement
~280GB — not a tuning problem, a defect.

## Contrast (isolates the defect)
The seed-compiled stage-4 lane (`stage4_is_seed` fallback in the bootstrap
script) compiles the identical 1777-file closure with a **flat ~90MB RSS**
(observed 89-94MB throughout). The blowup is specific to the self-hosted
compiler's own parse/AST retention, not to the source set.

## Repro
Bootstrap run at b69e5469531 + stage-4 unblock fixes (landed 625c4ce97c7):
stage2 → stage3 (both PASS self-host sanity) → stage3 binary drives stage-4
full-CLI build → watch RSS in `build/bootstrap/logs/.../stage4-native-build.log`.

## Lead
Per-file arena/AST is apparently never released between files in the
self-hosted driver's multi-file loop (seed's Rust driver releases per file).
Suspect the stage-4 driver path holds every file's parse tree live for the
whole build.

## Workaround in force
Bootstrap script's own seed-compiled stage-4 fallback lane (which then hit its
own separate crash — see bootstrap_stage4_seed_compiled_full_cli_run_test_crash_2026-07-20).

## UPDATE 2026-07-20 (root-fix lane): reproduced on the real path with the real
## binary; three specific hypotheses tested and REFUTED with direct evidence
## (array-clear-no-op, Dict-insert-O(n), env-mirror-active-in-prod). Two
## mechanisms remain live and UNDISCRIMINATED: (a) per-file O(n²) lexer/parser
## cost driving allocator high-water-mark churn, and (b) genuine cross-file
## retention — the real-corpus run's own ~36MB/file *steady* climb across
## wildly-varying file sizes (377–25717 chars) cuts toward (b), not (a) (a
## pure-churn mechanism would step only when a new largest-so-far file
## appears, not climb steadily regardless of size — see "leading hypothesis"
## below for the full discussion). No validated in-tree fix landed — see "why
## no fix shipped" below. **Next session: run the cheap discriminator
## (heap_registry-instrumented rebuild) before investing in a lexer rewrite.**

### Binaries used (state explicitly per the landmine)
- **Diagnosis binary:** `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
  (existing artifact, mtime 2026-07-18 01:32, sha confirmed built from a commit
  that is an ancestor of both `625c4ce97c7` and this session's worktree HEAD
  `def5305fb5f` — i.e. it already contains the stage-4 unblock fixes this bug's
  repro depends on). This is a genuine STAGE-3 SELF-HOSTED binary (cranelift
  backend), not the Rust seed — confirmed via `--version` / usage text and via
  the fact it reproduces the bug the seed does not.
- **Never reproduced/verified on:** any binary containing this session's
  source edits. Building such a binary requires stage2→stage3 from this
  worktree or compiling `main.spl`'s ~1292-file closure through the existing
  stage3 binary — both are the expensive operation this bug is about, and a
  partial such build (using the *existing* stage3 as compiler) was attempted
  and hit the exact same wall documented in
  `stage3_selfhost_parser_case_multielem_pattern_2026-07-17.md`
  ("very slow, ~5-6s/file sequential parse+convert"). See "Methodology
  pitfall" below — this also invalidated an earlier draft of this update that
  compared "baseline vs fix" runs of the *same* stage3 binary and wrongly
  read the near-identical numbers as "the fix barely helped."

### Reproduction (cheap, real command, real binary)
Ran the exact production stage-4 command
(`bootstrap_native_build_main` in `scripts/bootstrap/bootstrap-from-scratch.sh`)
against the existing stage3 binary, isolated cache/output dirs, external
`/proc/PID/status` VmRSS sampling (1 Hz) + a safety watchdog (this shared host
was concurrently under 90-110GB usage from other sessions the whole time):

```
env SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_COMPILER_PHASE_PROFILE=1 \
    SIMPLE_NATIVE_BUILD_THREADS=4 SIMPLE_RUNTIME_PATH=<rust target/bootstrap> \
    SIMPLE_BINARY=<stage3> \
  <stage3> native-build --target x86_64-unknown-linux-gnu --backend cranelift \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
    --entry-closure --low-memory --threads 4 --mode one-binary \
    --entry src/app/cli/main.spl -o <out>
```

`SIMPLE_COMPILER_PHASE_PROFILE=1` makes `log_phase()` (driver_log_helpers.spl)
print `[BOOTSTRAP-PHASE] +<ms> <event>` to **stderr** — a prior-session note
("native-build eprint lost") warns that worker stderr is dropped on some
native-build shapes (process-forked workers), but this run is confirmed
single-PID for the whole frontend/parse phase (matches the sibling bug doc's
own finding), so stderr *is* captured here when redirected. Sample, RSS in KB, correlated by epoch
against `phase2:parse:file:done` lines:

| after N files parsed | file | chars | RSS (approx) |
|---|---|---|---|
| 0 (phase1 done, before any file parsed) | — | — | ~3.86 GB |
| 17 | `src/app/play/main.spl` | 10406 | ~4.48 GB |

- Phase 1 (`load_sources_impl`, reading 1779 files' raw text into
  `self.ctx.sources`) alone takes the process from a ~1.6GB cold-start
  baseline to ~3.86GB in ~34s — **before a single file is parsed**. This is
  the "hold everything's raw source text" cost the mission anticipated.
- Phase 2 (actual parsing) then adds ~620MB over the first 17 files (~36
  MB/file marginal in this window) — smaller than the bug's reported
  ~160MB/file *average by file 403*, consistent with the growth **not** being
  file-count-linear-and-constant; see "per-file scaling" below for why.
- Individual file parse **times** are the more striking, decisive signal:
  a 19,414-char file took 8.5s; a 25,717-char file took 19.9s. `ms/char`
  climbs with file size across this window (0.2 → 0.48 ms/char, 13KB → 22KB
  files) — a super-linear-in-file-size signature, not a fixed per-char cost.

### Ruled out (evidence, not guesses)

1. **`.clear()` on module-level `var [T]` arrays not taking effect (the
   well-known "arrays are value types" landmine) — REFUTED.** Built and ran
   a minimal repro (`clear_test.spl`: fill a global `[i64]`, call `.clear()`
   from a different function with no reassignment, refill) through the
   stage3 binary via `native-build` (cranelift, `core-c-bootstrap` bundle).
   Output: `after_fill len=5` / `after_clear len=0` / `after_refill len=5` —
   correct on both the seed and the native-compiled path. `ast_reset()` →
   `stmt_reset()`/`expr_reset()`/decl-array resets (module_state.spl,
   ast_stmt.spl, `_AstExpr/nodes.spl`) all use exactly this bare-`.clear()`
   pattern and are confirmed wired into `parser_init_with_path()`, called at
   the top of every file's parse — the flat-AST parser scratch arenas
   (`stmt_*`, `expr_*`, `decl_*`, `arm_*`, `elif_*`) genuinely reset per file.
2. **`Dict<text, T>` assignment being O(current-size) per insert (copy the
   whole dict on every `dict[k]=v`) — REFUTED.** Built a synthetic
   `Dict<text, Big>` growth test (`Big` = a 2000-i64 array, ~16KB) via
   `native-build`, ran with N=50/100/200/400 inserts, measured peak RSS via
   `/usr/bin/time -v`: 3840 / 4864 / 6400 / 9728 KB. Marginal cost per insert
   is ~15-20KB across all three deltas — matches `Big`'s own size almost
   exactly, i.e. insert cost is O(1) amortized, not O(dict size).
   `self.ctx.modules[name] = module` accumulating across the closure is not
   quadratic by this mechanism.
3. **`SIMPLE_NATIVE_ARENA_DECLS` env-mirror (stmt/expr/decl fields mirrored
   into real `setenv()` calls when unset) being silently active in
   production — REFUTED.** This mechanism is real (ast_stmt.spl
   `stmt_env_mirror_enabled()`, `_AstExpr/nodes.spl`
   `expr_env_mirror_enabled()`, `_Ast/decl_nodes.spl`
   `ast_decl_env_mirror_enabled()` all gate on `SIMPLE_BOOTSTRAP=1 and
   SIMPLE_NATIVE_ARENA_DECLS != 1`), and it is **not** set by
   `bootstrap_native_build_main()` in the wrapper script for stage2/stage3.
   But `run_native_build_bootstrap()` in `src/app/cli/bootstrap_main.spl`
   (lines ~171-204) *does* set `SIMPLE_NATIVE_ARENA_DECLS=1` for exactly the
   `--entry src/app/cli/main.spl` + `SIMPLE_BOOTSTRAP_STAGE4=1` +
   `--mode one-binary` shape stage4 actually uses (confirmed: this routes
   through the in-process `aot_native_project_with_backend_fixed`, not the
   Rust `rt_native_build` FFI), and the sibling bug doc confirms this phase
   is single-PID (no worker-process env-visibility race). `git log -S
   'SIMPLE_NATIVE_ARENA_DECLS' -- src/app/cli/bootstrap_main.spl` shows the
   guard (`48921b1f924 perf(bootstrap): reuse flat AST arenas`) is an
   ancestor of the repro commit `625c4ce97c7` — the guard predates and covers
   the crash. This IS a real footgun on OTHER native-build entry points
   (anything not `main.spl`+STAGE4, e.g. plain `--entry <file>` builds) — see
   "Secondary finding" below — but it is not this bug's cause.

### Methodology pitfall discovered mid-investigation (record for future sessions)
Attempted to validate a candidate fix by editing `driver.spl` in-worktree and
re-running `<stage3-binary> native-build --entry main.spl ...` — i.e. asking
the *existing* stage3 binary to compile the *edited* source. **This does
not test the fix.** `stage3` is a frozen, already-compiled binary; when it
compiles `main.spl`'s closure (which happens to include `driver.spl` as one
of its own inputs), it does so using **its own already-compiled-in
driver.spl logic from when stage3 itself was built** — the on-disk edited
`driver.spl` is just input *bytes* being read and compiled into the *output*
binary, with zero effect on how the *currently running* stage3 process
manages its own memory. Two runs (unedited source vs. edited source, both
compiled by the same stage3 binary) produced near-identical RSS/timing
(4.48GB vs 4.34GB at the 17-file mark) for exactly this reason — the
comparison never touched the fix. **A driver-memory fix can only be observed
by building a binary FROM the fixed source and then running that new binary**
— i.e. the same expensive full-closure build this bug is about. This is the
same wall the `stage3_selfhost_parser_case_multielem_pattern_2026-07-17.md`
investigation hit twice with two different candidate fixes (both implemented,
compiled in, confirmed present via `strings`, and empirically shown to change
nothing on the real pipeline). Future sessions: do not trust a
"baseline vs fix" comparison unless the *fix* binary was built by a compiler
that already contains the fix (bootstrap one more stage), or unless the
change is validated on a **standalone repro that doesn't route through the
frozen binary's own compiled-in logic** (see the size-sweep below, which
*is* valid because it exercises the frozen binary's own real lexer/parser
directly — no self-hosting indirection).

### Leading hypothesis (evidence-backed, NOT yet fixed): per-file O(n²)
### lexer/parser cost — candidate mechanism, NOT confirmed to be the whole
### story; a genuine retention component has NOT been ruled out
This single-file measurement below is a genuinely different mechanism than
"AST held live too long" and matches a pre-existing, independently-noted
landmine (`feedback`/project memory: "Lexer O(n²) parse perf ... char_at
re-fetches whole source + O(n) slice per peek"). But it answers a narrower
question than the bug: each size-sweep point below is a **separate process**,
so it can only show a single file's own peak-RSS-vs-size relationship — it is
structurally blind to whether RSS given back between files in a *multi-file*
run. The real-corpus measurement above (~36MB/file steady climb over 17 files
ranging 377–25717 chars, not correlated with each file's own size) is the
only multi-file evidence collected, and it leans toward accumulation, not
pure high-water-mark churn: churn-from-transient-allocation would produce a
step function (RSS jumps when a new largest-so-far file is parsed, flat
otherwise), not an approximately-constant per-file add regardless of size.
Treat "O(n²) lexer churn" and "cross-file retention" as two open candidates,
not a settled conclusion — the discriminator neither rules in nor out below.

**Decisive, cheap, real-binary measurement** (no rebuild needed — exercises
the *existing* stage3 binary's own compiled lexer/parser directly on
synthetic single files, sidestepping the methodology pitfall above):
generated synthetic `.spl` files of increasing size (N repeated trivial
`fn f_i() -> i64: val a=i \n val b=i \n a+b` blocks) and compiled each alone
via `<stage3> native-build <file> --backend cranelift`, `/usr/bin/time -v`:

| funcs | bytes | wall time | peak RSS |
|---|---|---|---|
| 200 | 12,070 | 1.51s | 84.5 MB |
| 500 | 30,670 | 6.37s | 175.2 MB |
| 1000 | 61,670 | 31.00s | 340.5 MB |
| 2000 | 126,670 | **>120s (timed out)** | — |

Size ratio 500→1000 is 2.0x; **time** ratio is 4.87x (≈ size^2.28 — clearly
super-linear/quadratic, not linear). **RSS**, by contrast, tracks size almost
linearly across the same steps (2.07x, then 1.94x) — i.e. a *single* file's
peak memory is roughly proportional to its own size, not exhibiting runaway
growth on its own. This cleanly separates two different symptom classes:

- **Time:** confirmed quadratic-or-worse in file size, on the real compiled
  lexer. `lex_source_char_at`/`lex_source_slice`
  (`src/compiler/10.frontend/core/lexer.spl:191-207`) each call
  `current_core_source_get()` (line 396) and then slice the *full* source
  text (`source[pos:pos+1]`) for every character/token read. If text slicing
  in this runtime is not an O(1) view but scales with the source length (or,
  worse, if the module-slot fast path in `current_core_source_get()` misses
  and it falls through to re-reading the file from disk via
  `rt_file_read_text` at line 405 — not confirmed which path is hit in
  practice), a lexer making ~N such calls over an N-character file is O(N²).
  This matches the measured ms/char trend growing with file size in the
  real-corpus run above.
- **Memory — candidate explanation, weaker evidence than the time finding
  above, and in tension with the multi-file data:** a single file's *own*
  transient parse cost is ~O(file_size) and not, by itself, unbounded, so one
  *possible* explanation for the multi-file 64GB crash is **heap
  fragmentation / high-water-mark RSS from O(n²) allocation churn** rather
  than live-object retention — each file's parse makes many transient
  allocations (from the repeated slicing), and even if all are correctly
  freed back to the allocator between files (consistent with finding #1
  above — the tracked arenas genuinely reset), most allocators do not return
  freed pages to the OS, so RSS could reflect a churn high-water-mark rather
  than current live data. **However**, this predicts a *step function* across
  files (RSS rises only when a new largest-so-far file is parsed, flat
  otherwise) — and that is NOT what the real-corpus run shows: RSS climbed
  by a roughly constant ~36MB over each of the first 17 files despite those
  files ranging 377 to 25,717 chars (a 68x size spread with no corresponding
  step pattern in the sampled deltas). A roughly-constant per-file add
  regardless of size is the classic signature of **accumulation
  (retention)**, not size-dependent transient churn. The synthetic
  size-sweep cannot adjudicate between these because each point is a
  separate process (see header note above) — it only rules out "a single
  file's own parse is unbounded," it says nothing about what carries over
  between files. Both mechanisms remain open; do not treat "O(n²) churn" as
  confirmed over retention.

**This was not confirmed with an object-count signal** (e.g. `rt_heap_registry_count()`, already threaded into every
`log_phase()` call via `driver_log_helpers.spl`) that would prove "flat
object count, climbing RSS" vs "climbing object count" — the existing stage3
binary predates that instrumentation (`heap_registry=` does not appear
anywhere in either captured log), and building a binary that has it requires
the same expensive full-closure rebuild the methodology pitfall above
describes. **This is the single most valuable next step**: bootstrap one
fresh stage2→stage3 (or resume the shared host's existing in-flight
bootstrap once contention allows) and re-run the real command with the
`heap_registry` field now compiled in, and re-run the synthetic size-sweep
inline in-process (as a Simple test) to get before/after object counts per
file directly.

### Why no fix shipped in this pass
The two most plausible, actionable fixes both carry real, unvalidated risk
given the tools available this session:

1. **Fix the lexer's O(n) `char_at`/slice cost** (make
   `current_core_source_get()`/`lex_source_char_at` use an O(1) indexed
   character-code array — `lex_source_set()` already builds exactly such an
   array, `lex_source_codes`, but `lex_source_char_at`/`lex_source_slice`
   don't appear to read it) — this is squarely the mission's "fix at root"
   target, but it is hot-path code shared by every parse in the whole
   compiler (interpreter, seed-adjacent tooling, everything). A change here
   needs full-suite validation this session's remaining budget could not
   afford (the sibling bug doc's own attempts at smaller, more contained
   fixes in this exact neighborhood were both implemented, compiled in, and
   **empirically proven to change nothing on the real pipeline** — twice).
   Recommended as the next session's primary task, gated on getting the
   `heap_registry` signal first to confirm this diagnosis before investing
   in the lexer rewrite.
2. **Per-file source-text eviction** (drop `source.content` right after that
   file's own `parse_full_frontend` call, instead of waiting for the
   corpus-wide `evict_sources()` sweep at the very end of phase 2) — this
   *was* implemented in this session (`driver.spl`,
   `parse_all_impl`/entry-closure branch and the general bulk-loop branch),
   compiled successfully via the stage3 binary (no syntax errors), and
   matches the mission's own explicit "drop source text" fallback guidance.
   **It was reverted before commit**, for a concrete reason found by code
   reading, not speculation: `driver_native_sources_fingerprint()`
   (`driver_aot_output.spl:113-123`) hashes `source.content` to build the
   native-build object-cache scope key
   (`driver_aot_output.spl:286`, called during codegen/output, well after
   phase 2). Evicting `content` to `""` per file during phase 2 would make
   every source hash to the same "empty" fingerprint under `--low-memory`,
   silently defeating cache-key content-sensitivity (stale object reuse
   across genuinely different source versions) — a correctness regression
   that this session had no budget to also validate a fix for. The diff is
   preserved below as a proposed, NOT-landed patch; a future session should
   either (a) compute `driver_native_sources_fingerprint` before phase 2's
   eviction and cache the result, or (b) hash path+module_name+a
   content-length/mtime proxy instead of raw content, then re-apply and
   validate this eviction.

<details>
<summary>Proposed, unvalidated patch: per-file source-text eviction (NOT applied)</summary>

In `src/compiler/80.driver/driver.spl`, `parse_all_impl()`:
- Right after `unique_entry_sources` is computed, if `self.ctx.options.low_memory`:
  `self.ctx.sources = []` (the original bulk `--source`-scan list is fully
  captured into `entry_sources`/`unique_entry_sources` by that point and
  never read again in this function).
- In the `unique_entry_sources` parse loop, immediately after
  `parse_full_frontend(source.content, ...)` returns, if `low_memory`:
  reassign `unique_entry_sources[idx] = SourceFile(path: source.path,
  content: "", module_name: source.module_name)` (requires converting the
  `for source in unique_entry_sources:` loop to an indexed `while` loop —
  array-of-struct elements need index-assignment to mutate in place, not a
  `for`-loop binding).
- In the `entry_sources` module-registration loop (also converted to
  indexed), same content-clear per element, before `self.ctx.sources =
  entry_sources`.
- Same pattern in the non-entry-closure bulk branch, but must mutate
  `self.ctx.sources[idx]` directly (not the `val sources = self.ctx.sources`
  local binding) since that branch never reassigns `self.ctx.sources` at
  the end.
- **Must also fix `driver_native_sources_fingerprint`** before this is safe
  to land, per the correctness gap above.

</details>

### Diagnostic instrumentation landed (safe, level-gated, kept) — compile
### status: NOT independently re-verified after the eviction-fix revert
The (now-committed) probe-only diff is a strict subset of an earlier combined
diff (probe + the reverted per-file eviction change from item 2 above) that
did compile cleanly end-to-end via the stage3 binary. But no separate
compile run was done on the final, probe-only `driver.spl` by itself after
the eviction code was removed — a standalone syntax re-check attempted late
in this session (`native-build --source src/compiler/80.driver --entry
driver.spl --entry-closure`) hung/timed out (import closure pulls in most of
the compiler; scoping `--source` to only `80.driver` doesn't contain it, and
a full closure build is the same expensive operation this bug is about — see
"Methodology pitfall"). Landing lane / next session: treat this as unverified
until either a full stage3→stage4 rebuild succeeds with it in the tree, or a
narrower standalone syntax check is found. Risk is judged low (the added code
is a plain `fn`, an `extern`, and `print` calls, matching already-compiling
patterns elsewhere in this file and `driver_source_loading.spl`), but "low
risk" is not "verified."

`driver.spl` gained an env-gated (`SIMPLE_PARSE_RSS_PROBE=1`, default off)
per-file RSS probe in both `parse_all_impl` branches, printing to **stdout**
(`print`, not `eprint`/`log_phase`) since worker stderr is unreliable on some
native-build shapes. Shells out to `grep VmRSS /proc/self/status` rather than
using `rt_heap_registry_count()`/timing internals, because `text.to_i64()` was
found to be **broken on this native/cranelift path** — `"12345".trim().to_i64()`
returned `675995905`, not `12345`, when compiled and run via the stage3
binary (isolated repro: `rt_run_test/t.spl`). This is a real codegen defect,
now filed on its own:
[native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20](native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20.md)
(confirmed reproducible with a bare 2-line `main()`, no `rt_process_run`
involved — `n=<value:0x3039>` for the un-trimmed literal, i.e. the correct
integer 12345 is inside a tagged box that print-interpolation fails to
unwrap; a second, non-constant wrong value for the `.trim()`-routed variant).
Same family as `hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`.
The probe therefore returns/prints the raw grep text rather than a parsed
`i64`, sidestepping this defect rather than depending on it.

### Secondary finding (not this bug, filed for record)
`SIMPLE_NATIVE_ARENA_DECLS` is only set to `1` by the two call sites in
`bootstrap_main.spl`/`compile_targets.spl` that explicitly opt in
(`src/app/cli/main.spl` + `SIMPLE_BOOTSTRAP_STAGE4=1`, and the
`compile_targets.spl` native-single-file path). Any OTHER `SIMPLE_BOOTSTRAP=1`
native-build invocation (e.g. `native-build --entry <file>` without those
exact conditions, which falls through to the Rust `rt_native_build` FFI path)
runs with stmt/expr/decl env-mirroring silently ON — every parsed statement,
expression, and several decl fields (`NAME`, `PARAM_NAMES`, `PARAM_TYPES`,
`TYPE_PARAMS`, `BODY`, `IMPL_TRAIT` are mirrored unconditionally whenever
`SIMPLE_NATIVE_ARENA_DECLS != 1`, per `decl_nodes.spl:138`) gets written into
real process environment variables via `setenv()`, which are never cleared
between files. Confirmed not to affect this bug's specific repro, but is a
plausible, real memory/perf hazard on other bootstrap-mode entry points and
worth its own investigation.

## Guard script
`scripts/check/check-stage4-selfhost-parse-memory.shs` — compiles a small,
generated, single synthetic `.spl` file (repeated trivial functions, size
configurable) through the deployed self-hosted `bin/simple native-build`
and fails if wall time or peak RSS exceed documented ceilings. This targets
the *confirmed* per-file O(n²) mechanism directly (single large file); it
does **not** reproduce the multi-file entry-closure accumulation dynamics
(that requires the full ~1777-file closure to trigger cleanly per the
sibling bug doc's own findings) — see the script's own header comment for
the exact scope and how to widen it once the `heap_registry` signal
disambiguates retention vs. allocator-churn.

**Validated against the stage3 binary** (`STAGE4_PARSE_MEM_BINARY=<stage3>
STAGE4_PARSE_MEM_TIME_MAX_S=30 sh scripts/check/...shs`), both the pass path
(200-func file, 135968 KiB peak, well under the 512MB default ceiling) and
the fail path (same run, artificially tight 1000 KiB ceiling → correctly
reports `error=peak_rss_kib:135968 exceeds ceiling 1000` and exits 1).
**Not validated against the actual default, `bin/simple`**: the currently
deployed `bin/simple` fails `native-build --entry <file>` even on a trivial
`fn main() -> i64: 0` entry with `error: semantic: function expects 2
argument(s), but more were provided`, reproduced with both `--mode
one-binary` and `--mode dynload`, with and without `--backend cranelift`.
This is content-independent (same error on a 1-line file and a 30-function
file) and therefore a separate, pre-existing `bin/simple` defect unrelated
to this bug — not investigated further here (out of this task's scope), but
it currently blocks running this guard script against its own documented
default binary. Filed as a TODO in the script itself; use
`STAGE4_PARSE_MEM_BINARY=<a working self-hosted binary>` until it's fixed.

## UPDATE 2026-07-20/21 (discriminator lane): RETENTION, confirmed via a real
## live-object counter — not allocator churn. Two lexer-side hypotheses
## (`lex_source_char_at`/`lex_source_slice` re-slicing; `lex_state_get`/
## `lex_state_set` getenv/setenv-per-char) were implemented and BOTH measured
## ~0% improvement — both turned out to be on a dead code path the real
## `SIMPLE_BOOTSTRAP_STAGE4=1` build never exercises (see "CORRECTION" below).
## Root mechanism is actually localized to `parse_module_body` (flat-array
## core-parser AST node construction) via per-sub-phase `heap_registry`
## markers — see "Actual dominant mechanism" below for the table.

### Discriminator result (the "next step" the prior update asked for)
Built a fresh self-hosted binary containing `log_phase()`'s
`heap_registry=rt_heap_registry_count()` field (absent from every binary
available at session start — none post-dated commit `43a219d2889`, which
added it) and re-ran the exact real production command from this doc's own
"Reproduction" section above (`SIMPLE_BOOTSTRAP_STAGE4=1`,
`--runtime-bundle core-c-bootstrap`, `--entry src/app/cli/main.spl`,
`--mode one-binary`, `--low-memory`), killing early instead of letting it
run to the 1777-file/64GB crash.

**Binary provenance:** stage2 (seed-compiled, NOT stage3) built from worktree
HEAD `26a5e7394074836c2e2741d4b97f0a1ebb6ddd82`. Stage2 is a valid proxy here
because the bug is about the *behavior of compiled Simple code* (driver.spl/
lexer.spl running as native cranelift output), not about which stage compiled
it — confirmed empirically: this stage2 run reproduces the same growth
profile the doc's earlier stage3-binary measurements found. The Rust runtime
lib (`--runtime-path`) was borrowed **read-only** from a sibling lane's
worktree (`/tmp/wt_fat32lfn`) that happened to be built from the exact same
commit — avoided a from-scratch Rust rebuild (~9GB target dir, infeasible
under this session's disk budget). Seed binary used only to drive the
`native-build` invocation; the seed itself is never the thing being measured.

**First `rt_heap_registry_count()` semantics check (prerequisite before
trusting the discriminator at all):** read
`src/compiler_rust/runtime/src/value/heap.rs:186-212`. The registry is a real
`HashSet`-backed live-pointer set with `insert`/`remove` on
`register_heap_ptr`/`unregister_heap_ptr`; `rt_heap_registry_count()` returns
`registry.len()`, i.e. **current live objects**, not a monotonic
allocation total. A climbing count is therefore a genuine retention signal,
not an artifact of the counter's own design. (The same file's own doc
comment: *"most no-GC compiler temporaries stay registered for the process
lifetime"* — i.e. this runtime tier has no generic reclaim; something must
explicitly `unregister_heap_ptr`/free, or it lives until process exit.)

**Per-file table** (binary: stage2 built from this session's worktree,
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, run via
`SIMPLE_BINARY=<itself>`, entry `src/app/cli/main.spl`, killed after 345
files rather than let it reach the 1777-file/64GB crash):

| file # | t (ms) | heap_registry | path |
|---|---|---|---|
| 1 | 5,958 | 515,083 | src/app/cli/main.spl |
| 5 | 9,235 | 873,392 | src/app/io/env_ops.spl |
| 10 | 11,299 | 1,148,611 | src/app/io/_CliCommands/handler_commands.spl |
| 20 | 18,621 | 1,924,067 | src/app/play/main.spl |
| 50 | 71,700 | 5,142,304 | src/lib/nogc_async_mut/database/test.spl |
| 100 | 137,443 | 9,985,123 | src/app/devhub/cmd_email.spl |
| 150 | 146,933 | 11,406,328 | src/std/nogc_sync_mut/io/volatile_ops.spl |
| 345 (killed) | 450,357 | 29,384,462 | src/compiler/backend/backend_port.spl |

Delta: +28,869,379 live objects over 345 files = **83,923 objects/file
average**, essentially linear (not step-function, not size-correlated —
matches the prior update's own "constant per-file add regardless of size"
observation, now confirmed against a true live-object count instead of just
RSS). RSS was independently sampled via `/proc/<pid>/status` and tracked
`heap_registry` closely (tens of GB by the time the process was OOM-killed
mid-file, same failure mode as the original 64GB/403-file report, just
reached faster here because this run wasn't `--threads 4`-throttled the same
way and had no competing safety margin). This **directly answers the prior
update's open question**: live object count climbs monotonically and
steadily → **RETENTION**, not allocator high-water-mark churn from transient
per-call slicing.

### Root-cause localization: it is NOT `lex_source_char_at`/`lex_source_slice`
The prior update's leading (but explicitly unconfirmed) hypothesis was
`lex_source_char_at`/`lex_source_slice` (`lexer.spl:191-207`) re-slicing the
full source `text` per call — confirmed real and O(N) per call (UTF-8 char
indexing rescans from byte 0;
`src/compiler_rust/runtime/src/value/collections.rs:1803`
`rt_string_char_at` does `s.chars().nth(index)`), and each call allocates a
fresh heap-registered string. This was **fixed** (see `lexer.spl`,
`lex_source_char_at`/`lex_source_slice` now index
`current_core_lexer_slot[0].source_chars`/`.char_slice()` — an existing,
already-correct, O(1)-indexed, per-file, UTF-8-safe structure built by
`make_core_lexer()`, `lexer_struct.spl:104-201`, that the codebase already
had but the legacy free-function lexer never used) and **verified hot**
(confirmed via a one-shot debug print that the new code path fires on the
real corpus, not a vestigial branch — `lex_peek`/`lex_peek_next`/
`lex_peek_at`/`lex_advance` all route through `lex_source_char_at`).

**But it made ~no measurable difference**: rebuilding stage2 from the fixed
source and re-running the identical discriminator produced **86,809
objects/file** over 334 files — statistically the same slope as the 83,923
baseline above, not a reduction. Conclusion: the O(N) re-slice was real and
worth removing (it's still a legitimate, if minor, algorithmic fix — kept in
tree), but it is **not the dominant contributor** to the retained-object
count. Do not re-attempt this fix path expecting a different result; the
data says no.

**CORRECTION (same session, before this doc was first saved to disk): the
next hypothesis below was ALSO tested and ALSO produced ~0% improvement —
101,082 -> 104,996 objects/file over the identical first-40-files window.
The reason both "fixes" did nothing is that they were edited on a DEAD
CODE PATH.** `lex_next()` (`lexer.spl:786-798`, the function `parser_advance`
actually calls to get each token) does `loaded.next_token()` where
`loaded = current_core_lexer_slot[0]` — the `CoreLexer` **struct's own**
`next_token()` method (`lexer_struct.spl`), not the free-function scanners
(`lex_scan_token`/`lex_scan_ident`/etc., `lexer_scanners.spl`) that call
`lex_peek`/`lex_advance`/`lex_source_char_at`. Grepped: `lex_scan_token`,
`lex_peek`, `lex_advance` have **no callers outside `lexer_scanners.spl`
and `lexer.spl` themselves** — the entire free-function lexer (including
both "fixes" above) is vestigial on the real `SIMPLE_BOOTSTRAP_STAGE4=1`
build path. `current_core_lexer_save()`, which would mirror `CoreLexer`
state back into the env vars the free functions read, is itself gated
`if not lex_env_save_enabled[0]: return` and that flag defaults false. This
is why the one-shot debug print "proved hot" (it *was* called — once, at
whatever incidental call site still reaches it — just not on the
per-character path that dominates object count) and why both rebuilds
moved nothing. **Both edits are kept in tree** (real, harmless, honestly
worthless for this bug — see the corrected status below) rather than
reverted, since a mid-session revert would have cost another rebuild this
session's disk budget (final free space: ~3.4GB, shared host, actively
falling) could not safely afford.

### Actual dominant mechanism: `parse_module_body` (flat-arena AST node
### construction), not the lexer at all
Added env-gated (`SIMPLE_COMPILER_PHASE_PROFILE=1`) `heap_registry`
sub-phase markers inside `parse_full_frontend` (`frontend.spl`) and inside
`parse_and_build_module` (`module_assembly.spl`), splitting each file's
parse into `preprocess` / `reset_all_pools` / `parser_init_with_path` /
`parse_module_body` / `flat_ast_to_module` / `desugar_module` /
`desugar_collections`. Re-ran the real corpus (same binary-provenance
method as above — stage2 rebuilt from this source, killed after 20 files).
Per-file delta by sub-phase (objects; `chars` = source size):

| file | chars | preprocess | reset_pools | parser_init | **parse_module_body** | flat_ast_to_module | desugar | total |
|---|---|---|---|---|---|---|---|---|
| main.spl | 773 | 23 | 13 | 82 | **1,584** | 93 | 30 | 1,861 |
| log_modes.spl | 5,747 | 23 | 15 | 76 | **56,404** | 7,816 | 74 | 64,447 |
| args_and_os_commands.spl | 11,437 | 23 | 15 | 80 | **71,455** | 7,982 | 108 | 79,702 |
| main_and_help.spl | 21,837 | 23 | 15 | 91 | **179,884** | 17,095 | 90 | 197,237 |
| env_ops.spl | 2,735 | 23 | 15 | 79 | **18,452** | 2,270 | 90 | 20,968 |
| cli_ops.spl | 13,512 | 23 | 15 | 85 | **85,539** | 7,917 | 244 | 93,839 |

`parse_module_body` is **85-95% of every file's total** and scales with
source size (~6-10 objects/char, consistent across a 773-21,837 char
range); `flat_ast_to_module` is a distant second (~10% of
`parse_module_body`'s size, still size-correlated); `preprocess`,
`reset_all_pools`, `parser_init_with_path`, `desugar_module`,
`desugar_collections` are all flat, tiny, and irrelevant (tens to low
hundreds of objects regardless of file size). This is the same flat-array
core parser (`stmt_*`/`expr_*`/`decl_*`, `compiler.core.parser_decls`) the
very first "ruled out" item in this doc examined for its `.clear()`
behavior — that investigation confirmed the arrays' *length* resets
correctly per file, but never checked whether the *heap objects the
cleared slots used to point to* get unregistered, and per
`heap.rs`'s own doc comment ("most no-GC compiler temporaries stay
registered for the process lifetime") they do not unless something
explicitly calls `unregister_heap_ptr`/frees them — matching
`rt_array_free(retired.source_chars)` at `lexer.spl:179`, which is exactly
that explicit free, just not applied to the parser's own arenas.

**Status: localized, not fixed — a real fix here needs two more answers
this session's disk budget (final free space ~3.4GB, shared host, falling)
could not safely afford to get via rebuild-and-measure:**

1. **Copy vs. alias — partially read this session, leans ALIASED, not
   conclusively resolved.** `flat_ast_to_module` (`module_assembly.spl:114+`)
   walks flat decls via `module_decl_at(di)` and calls converters
   (`convert_decl_fn(idx)` etc., `convert_nodes.spl:1431+`) that build
   `Function`/`Struct`/`Stmt`/`Expr` values from arena getters. Read
   `decl_get_name` (`_Ast/decl_nodes.spl:664-668`): `return decl_name[idx]`
   — returns the array-indexed value directly, no explicit clone. Read
   `convert_decl_fn` (`convert_nodes.spl:1432`): `val name =
   decl_get_name(idx)`, then this flows straight into the built `Function`
   — again no explicit clone anywhere in the chain. **This does not by
   itself prove aliasing** (Simple's `text` is a value type at the language
   level; whether `val name = decl_get_name(idx)` is a real memcpy-backed
   copy or a shared-pointer copy is a property of the *runtime's* value
   assignment for heap-backed `text`, not of this `.spl` code, and that
   wasn't checked this session — it's the one remaining fact that would
   flip this from "leans aliased" to "actually determined"). Given: (a) no
   explicit clone/copy call anywhere in the getter-to-converter-to-Function
   chain, (b) this runtime has no refcounting (`heap_allocation_registry`
   is a plain insert/remove set, not a refcounted map — see the `heap.rs`
   citation above), and (c) the doc's own earlier finding that
   `rt_array_free` does a **real** `std::alloc::dealloc` (not registry-only
   bookkeeping) — the risk-weighted read is: **treat this as aliased
   (architectural) unless a future session finds a real memcpy at the
   `text` assignment boundary that contradicts it.** Do not attempt an
   arena-free fix without first finding that memcpy, or proving its
   absence some other way (e.g. a targeted repro: build a `Function`, free
   the source arena element via the runtime's `text`-level free primitive
   if one exists, and see whether the `Function`'s field is still valid).
2. **`rt_array_free` frees the array's own backing buffer, not its
   elements' own allocations.** Checked `src/compiler_rust/runtime/src/
   value/collections.rs:1438-1454`: `rt_array_free` does
   `std::alloc::dealloc` on the array's data buffer and header (a REAL
   free — a wrong call here is a genuine crash/corruption bug, not just a
   missed optimization) and calls `unregister_heap_ptr` for the array
   object itself, but does **not** recurse into unregistering each
   element's own heap allocation. For a `[text]` array (e.g.
   `current_core_lexer_slot[0].source_chars`, freed today at
   `lexer.spl:179`), this frees the N-pointer-slot buffer but leaves each
   of the N individual character-`text` objects registered/leaked. This
   means even the codebase's own existing "known-good" per-file free
   pattern is a partial win at best for that case, and any fix for the
   flat-AST arenas (`stmt_*`/`expr_*`/`decl_*` — many of which are almost
   certainly `[text]`/mixed-type arrays holding per-node string data) would
   need to free every element's own allocation, not just call
   `rt_array_free` on the outer array, to actually collapse the
   `heap_registry` growth this doc measures.

Given both of these are unresolved and `ast_reset()`/`stmt_reset()`/
`expr_reset()`/decl-array resets are **hot-path code shared by every parse
in the whole compiler** (interpreter, tooling, everything — a wrong answer
is a silent-wrong-binary or use-after-free class defect, not a perf
regression), and the prior update in this same doc already recorded two
separate adjacent attempts in this neighborhood that looked safe and were
not (`stage3_selfhost_parser_case_multielem_pattern_2026-07-17.md`), no fix
was attempted at this level this session. Next session: answer (1) via
read, then (2) via read of the arena field types (`compiler.core.ast*`
decl/stmt/expr field declarations), then validate any fix with a fresh
binary + the sub-phase markers already landed here (env-gated
`SIMPLE_COMPILER_PHASE_PROFILE=1`, zero cost when off) — not by guessing.

### Guard script #2: multi-file (the gap the original guard's own header
### flagged)
`scripts/check/check-stage4-selfhost-parse-memory-multifile.shs` — new,
lands alongside this update. The original guard script
(`check-stage4-selfhost-parse-memory.shs`) only exercises the single-file
O(N^2) time mechanism and explicitly documents that it does **not** catch
multi-file accumulation. This one does: generates a fixed, deterministic
chain of N synthetic files (`mod0` imported by `mod1` imported by `mod2`
... entry = `mod(N-1)`, so `--entry-closure` transitively reaches exactly N
files, no repo-root scan, no real-corpus dependency) and fails if whole-
build peak RSS (`/usr/bin/time -f %M`, same technique as the sibling
script) exceeds a documented ceiling. Same `bin/simple`-is-currently-broken
landmine applies — override with `STAGE4_PARSE_MEM_MULTI_BINARY=<a working
self-hosted binary>`.

**Calibrated and validated 2026-07-21** against the stage2 probe binary
built for the sub-phase localization above (self-hosted, not the seed):
40 files x 20 funcs/file, pass path measured **135,576-135,968 KiB peak**
(default ceiling 409,600 KiB, ~3x headroom — a defect-class tripwire, not a
tight budget); fail path (artificially tight 1000 KiB ceiling) correctly
reports `error=peak_rss_kib:135808 exceeds ceiling 1000 over 40 files` and
exits 1. This is a coarse whole-build signal (one peak-RSS number), not a
per-file slope — if it regresses, re-run with
`SIMPLE_COMPILER_PHASE_PROFILE=1` and grep `FRONTEND-SUBPHASE`/
`BOOTSTRAP-PHASE` output (both landed in this same update) to see which
sub-phase and which file(s) moved, rather than guessing from the aggregate
number alone. Not wired into CI — land + document only, per this session's
scope.

## UPDATE 2026-07-24: retention CONFIRMED by the heap_registry discriminator
## (the "single most valuable next step" above has now been run)

Two real-corpus Stage-4 one-binary runs on macOS aarch64 (24GB RAM), using a
fresh stage2 built 2026-07-24 (which, unlike the 07-20 binaries, HAS the
`heap_registry=` field compiled into every `BOOTSTRAP-PHASE` line):

- Run A (dirty root, `build/stage4_onebin3_2026-07-24.log`): SIGKILL at ~12
  min while parsing `src/compiler/traits/trait_solver.spl`,
  `heap_registry=64,571,013`.
- Run B (clean detached worktree at 2b6ca665,
  `build/stage4_onebin4_2026-07-24.log` + 5s memory sampler
  `build/stage4_wt_mem_2026-07-24.log`): SIGKILL at 9m51s while parsing
  `src/app/ui.web/html.spl` (546,841 chars), `heap_registry=44,822,116` at
  that file's parse start. Sampler shows macOS grew swap 6GB -> 62GB in 10
  minutes until disk headroom ran out (last sample: swap used 62,267MB of
  62,464MB, process RSS ~2.2GB with the rest paged out, VSZ 508GB). Total
  dirty footprint at kill: ~80GB+ (24GB RAM + 62GB swap), still mid-phase2.

**Discriminator verdict: climbing object count = genuine cross-file
RETENTION, not allocator high-water churn.** The `heap_registry` live-object
count climbs monotonically file-after-file and never steps down between
files. Per-file deltas scale with each file's size at ~8 live objects per
source char, e.g. (all from run B):

| file | chars | heap_registry delta |
|---|---|---|
| `src/lib/common/base_encoding/base64.spl` | 8,723 | +71,017 |
| `src/lib/common/ui/web_render_api.spl` | 59,767 | +470,970 |
| `src/app/ui.render/html_widgets.spl` | 37,873 | +330,989 |

At ~44.8M live objects the swap-measured footprint was ~60GB, i.e. **~1.3KB
average per live heap object**. Projecting the full ~1777-file closure gives
~70M+ objects / ~90GB+ — structurally unable to fit on a 24GB machine
regardless of what else runs. The 07-20 "two open candidates" section is
therefore resolved: the O(n^2) lexer cost is real but is the TIME symptom;
the MEMORY kill is object retention (tokens/AST/interned slices held live at
~8 objects and ~10KB per 10-char line — grotesquely un-compact even if the
AST must legitimately survive until codegen).

Also confirmed 2026-07-24: splitting the single 109KB line in
`src/app/ui.web/html.spl` (commit 2b6ca665, separate parser bug) moved the
kill point PAST that file in run A — the two defects are independent.

Provenance note for future sessions: the deployed
`bin/release/aarch64-apple-darwin/simple` (Jul 11) was built by the
pre-2026-07-16 dispatch, which routed Stage-4 `--entry` through Rust
`rt_native_build` (`3a9d58fce2` rerouted it to the in-process pure-Simple
driver; that path has never completed a real Stage-4 build). Until the
retention defect is fixed, the Rust-FFI route (drop `SIMPLE_BOOTSTRAP_STAGE4=1`
so `bootstrap_main.spl` dispatches to `run_rt_native_build`) remains the only
build shape for the full CLI that fits on this class of machine.

Next steps, in value order:
1. Find WHAT retains: instrument or read `parse_full_frontend` callers —
   are per-file token arrays retained alongside the AST? Are text slices
   (token lexemes) each a separate boxed heap object? A token-array drop or
   lexeme interning could cut the footprint by an order of magnitude.
2. The lexer `char_at`/`slice` O(n^2) fix (`lex_source_codes` is already
   built but unused by `lex_source_char_at`/`lex_source_slice`,
   `src/compiler/10.frontend/core/lexer.spl:191-207`) — fixes the TIME
   symptom incl. the 60s-timeout giant-literal files; validate via the
   normal dynload bootstrap + both guard scripts.

## UPDATE 2026-07-24 (root-cause + fix lane): dominant mechanism FOUND at the
## codegen layer — native codegen boxed every STRING-LITERAL EVALUATION
## through rt_string_new. Fix = interned rt_string_new_literal, landed across
## seed cranelift/LLVM codegen + .spl cranelift adapter + Rust/C runtimes.

(This lands alongside — and answers — the macOS discriminator update above:
its "next steps #1: lexeme interning could cut the footprint by an order of
magnitude" is exactly what this fix implements, one layer lower.)

### Root cause (confirmed by code + profile, not conjecture)
The prior updates localized retention to `parse_module_body` (~6-10 objects
per source char) but stopped at the arena layer. The actual mechanism is one
layer down, in codegen, and explains the per-char scaling directly:

- **Every evaluation of a text literal allocates a fresh, permanently
  registered heap string.** Seed cranelift: `compile_const_string`
  (`src/compiler_rust/compiler/src/codegen/instr/collections.rs:408`) emits
  `rt_string_new(rodata_ptr, len)` inline — re-executed each time the literal
  expression evaluates. Same per-eval boxing at string-literal PATTERN tests
  (`codegen/instr/pattern.rs:48`) and fstring literal parts, and in the seed
  LLVM backend (`codegen/llvm/functions/consts.rs:61`, `functions.rs:1173`,
  `functions.rs:1866`). The .spl cranelift adapter has the identical shape
  (`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1029`).
  On this no-GC tier nothing ever unregisters, so each execution leaks one
  registered object.
- The parser is literal-comparison saturated (`tok == "fn"`,
  `case "NAME"`, keyword tables): a gdb sample profile of the deployed
  self-hosted binary parsing the multifile guard corpus put **8/12 samples in
  `rt_string_eq`** — dozens of literal comparisons per token, each also
  boxing its literal operand → tens of registered objects per token ≈ the
  measured ~8-9 objects/char, scaling with source size exactly as observed
  (including the macOS run B per-file deltas above).
- Fresh baseline (deployed `bin/release/x86_64-unknown-linux-gnu/simple`,
  Jul 24, multifile guard corpus, identical 1,548-char files):
  **~19,515 registered objects per file (~12.6/char)**, and per-file parse
  time **growing 1.16s → 6.7s** across the first 28 identical files (the
  guard script times out at 120s before finishing 40 files).

### Fix landed (this session)
1. **`rt_string_new_literal(ptr, len)`** — interned literal boxing keyed by
   the literal's stable rodata `(address, len)`; returns one shared boxed
   string for every evaluation of the same literal site. Added to the Rust
   runtime (`runtime/src/value/collections.rs`, exported via `value/mod.rs` +
   `lib.rs`, JIT/ELF symbol map `elf_utils.rs`, spec table
   `runtime_sffi.rs`, codegen-root list `common_backend.rs` — REQUIRED, else
   cranelift AOT panics `no entry found for key`) and to the C runtime
   (`src/runtime/runtime_native.c` + `runtime.h`, 65,536-bucket chained
   hash, spinlock, same idiom as the short-string cache). Static literal
   data ONLY — never reusable heap buffers.
2. **All literal-boxing call sites swapped** to the interned variant: seed
   cranelift (const/pattern/fstring), seed LLVM (const/pattern/fstring),
   .spl cranelift adapter const-Str; `stage4_symbol_closure.spl` contract
   lists extended. One-time global initializers (backend_core.rs) left as-is
   (they run once). The .spl LLVM text backend emits raw GEPs for consts (no
   per-eval boxing at the const site) — its `box_runtime_value` path in MIR
   lowering still uses rt_string_new because its operand is not provably a
   literal; follow-up noted below.
3. **Decl env-mirror contained** (the 07-20 "Secondary finding"):
   `ast_decl_text_set` mirrored six fields (NAME/PARAM_NAMES/PARAM_TYPES/
   TYPE_PARAMS/BODY/IMPL_TRAIT) into real `setenv()` env vars on EVERY run
   that didn't set `SIMPLE_NATIVE_ARENA_DECLS=1` — including plain
   native-build/test/LSP — plus a `rt_env_get_i64` environ scan per
   getter/setter call. Now: non-bootstrap runs default to arena-preferred
   (`ast_decl_arena_default()`, decl_nodes.spl); bootstrap lanes keep the
   legacy default because interpreter lanes rely on the env store (module
   vars may not persist under tree-walk interp — see stmt_env_mirror note);
   the flag is slot-cached and refreshed per file (module_state.spl reset);
   all 89 mirror call sites are wrapped in `if not ast_decl_prefer_arena():`
   so join-heavy arguments are not even computed when the mirror is off.

### Validation (2026-07-24, binaries built FROM the fixed source — per the
### methodology pitfall, both gates below use freshly built artifacts)
- **Probe gate (fixed seed, cranelift, core-c-bootstrap):** a 100,000-iteration
  loop doing 3 text-literal comparisons per iteration (300,000 literal
  evaluations) adds **4** registered objects total (pre-fix: one per
  evaluation ≈ 300,000). Control loop allocating 2,000,000 genuinely dynamic
  strings still registers each one, with flat per-batch time at 2M live
  objects (registry insert is O(1); allocator cost is not live-count-bound).
- **Multifile guard corpus** (`check-stage4-selfhost-parse-memory-multifile.shs`,
  40 files × 1,548 chars, `SIMPLE_COMPILER_PHASE_PROFILE=1`):

  | metric | baseline (deployed Jul-24 binary) | stage2 built from fixed source |
  |---|---|---|
  | registered objects/file | ~19,515 (~12.6/char) | **3,492 (~2.26/char)** |
  | per-file parse time | 1.16s growing to 6.7s; **timed out** at 28/40 files | **flat 360–544ms**, all 40 files |

- Stage2 build itself: 1,388 files compiled, 0 failed, 195s compile + 109s
  link (seed lane, threads 8). `--version` + `run` sanity pass (run needs the
  `simple_seed` sibling — pre-existing
  cli_symlink_argv0_seed_sibling_lookup_2026-07-24, unrelated).
- Stage2's own `native-build` emits objects through the .spl cranelift
  adapter (interned path) but cannot LINK on this host ("Hosted native
  linking is unsupported…") — pre-existing self-hosted link gap, fails
  identically with the legacy env-store mode forced
  (`SIMPLE_NATIVE_ARENA_DECLS=0` A/B), so not introduced here. The guard
  script's own RSS sample (`error=no_rss_sample`) is a casualty of that same
  pre-existing link failure; the registry/time data above comes from the
  fully-completed parse phase.
- Pre-existing, noted in passing: `rt_text_cmp_any` is missing from the
  JIT symbol map (`elf_utils.rs`) → `run` JIT falls back to interpreter with
  "unresolved external symbol 'rt_text_cmp_any'". Not introduced by this
  change (`rt_string_new_literal` IS in the map).

### Remaining ~2.26 objects/char (Stage 2/3 of the research plan — open)
Dominated by `source_chars: [text]` (1 text object per char, leaked at
CoreLexer retirement because `rt_array_free` frees only the outer buffer),
then per-token texts and per-node arena inner arrays. See
doc/01_research/compiler/parser/ast_memory_management_survey_2026-07-24.md
for the staged plan and
doc/00_llm_process/layer_expert/backend/skill.md for the codegen rules this
fix introduces. Status: **partially fixed — dominant mechanism removed,
5.6x objects/char reduction, per-file time flat; full-corpus stage4 lane
re-run still pending.**

## UPDATE 2026-07-24 (late): seed-binary clobber regressed the fix; probe attribution corrected

**Regression found + fixed.** `src/compiler_rust/target/bootstrap/simple` was
rebuilt at 14:38 by a parallel session from pre-fix source: `strings` shows
ZERO `rt_string_new_literal` references (the 11:44 fixed seed's probe still
interns: 300k literal evals → 4 objects; a probe built with the 14:38 seed
leaks 1 object per literal *evaluation* again — `val l = "xy"` = 10,000
objects / 10,000 iterations). Source in the working copy AND origin/main is
intact; only the binary was stale. Fixed by rebuilding the seed in place:
`cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap
-p simple-driver && … -p simple-native-all`. **Landmine for all sessions: a
seed rebuilt from any pre-571bb8f8be35 checkout silently reverts the parse
memory fix for every stage2 built afterward. Check
`strings -a target/bootstrap/simple | grep -c rt_string_new_literal` (>0)
before trusting memory numbers.**

**Residual-leak attribution corrected** (registry-delta probe, fixed seed,
core-c-bootstrap, 10k-char source):
- `chars()` on a 10k string: **1** object (the array). Single-byte strings are
  process-cached (`short_string_cache`), so `source_chars` per-char texts are
  NOT ~1.0/char as previously guessed — they are ~0.
- len-1 slices (`s[i:i+1]`): ~0 (cached path in `rt_slice` → `rt_string_new`).
- multi-char slices: exactly **1/slice** (genuine dynamic string — token texts).
- text `==` (dyn==dyn): **0** — equality does not allocate.
- concat: 1/op (genuine).
So the remaining ~2.26 objs/char in the multifile gate ≈ per-token slice texts
+ per-node arena inner arrays, i.e. Stage 2/3 of the research plan (span
tokens / per-file free), not a runtime cache gap.

## 2026-07-24 PM — independent re-validation (scaling harness) + redeploy gap

Triggered by a 4.5h self-host build with monotonic RSS→3.9GB. Built a synthetic
scaling harness (`/tmp/perfscan/{gen,run}.sh`: one file, G groups × 11 fns) and
measured native-build (cranelift, one-binary) vs input size:

| compiler binary | 3.2K ch | 12.5K ch | 25K ch | 101K ch | 412K ch |
|---|---|---|---|---|---|
| deployed `bin/release/.../simple` (01:22, pre-interning) | 1.9s parse | **22.9s parse → SIGILL @ lower_to_mir** | — | — | — |
| fresh cranelift bootstrap `stage3` (14:49) | 6.3s | 5.7s | 5.8s | 7.9s | 12.9s |

- Deployed binary: **O(n²)** parse (≈4× time per 2× input), ~18.6 heap objects/char,
  RSS 29→242MB super-linear, then crashes at MIR — the classic pre-interning wall.
  This is why the 4.5h build never finished: with 2,600 files it was stuck in
  **phase2:parse**, RSS climbing as the no-GC registry grew (it never reached codegen).
- Fresh bootstrap: **linear** — 412K chars in 13s (minus ~5.5s fixed link overhead:
  101K→412K = chars×4.06, var-time×3.08 ≈ linear, not ×16). Built binaries run
  correctly (input-dependent rc), not stubs.

**Redeploy gap (the actionable finding):** ALL available self-hosted binaries
(deployed, wt_fa 12:40, stage3 14:49) grep **0** for `rt_string_new_literal`
(not stripped — other rt_string_* symbols are visible), so the landed interning fix
(571bb8) is **not compiled into any binary yet**; stage3's linearity comes from the
lexer `source_chars` fix (102959c), not interning. The current bootstrap seed
`src/compiler_rust/target/bootstrap/simple` (17:33) DOES emit interning (grep=4) and
was verified to propagate it into an output binary (grep=1, runs rc=96).

**Action = redeploy, not new code:** rebuild the production self-hosted binary via
the interning seed (cranelift; `bin/release` swap intentionally deferred). Do NOT
native-build the whole compiler with the deployed pre-interning binary — that is the
O(n²) trap. Harness has no generics/monomorphization; a separate mono-phase O(n²),
if any, is not covered by this (the observed blowup was parse, which is fixed).

### Update — fresh interning binary built (315s) + recipe gotchas

Built the first self-hosted binary carrying the interning fix, via the interning
seed `src/compiler_rust/target/bootstrap/simple` (17:33, grep `rt_string_new_literal`=4),
cranelift one-binary of compiler+app+lib+10_tooling:
- Result: `/tmp/perfscan/fullbuild/simple`, grep **rt_string_new_literal=1** (all
  prior available binaries = 0 — this is the first). Build **315s total** (212s
  compile + 103s link, 1389 files, rc=0) — the correctly-configured **seed**-driven
  build; the 4.5h figure was the pre-fix self-hosted binary wrongly used as the
  compiler (~50× penalty). This alone demonstrates the practical fix: build via the
  Rust seed, never the deployed pre-interning binary.
- Recipe gotchas for the redeploy: `SIMPLE_NO_STUB_FALLBACK=1` + `SIMPLE_BOOTSTRAP_STAGE4=1`
  hard-fail the Stage4 symbol-closure at link on `rt_vulkan_*` (GPU externs the CLI
  pulls; no archive owner in core-c-bootstrap). Dropping STAGE4 +
  `SIMPLE_ALLOW_FREESTANDING_STUBS=1` links, but the STAGE4-stripped binary's CLI
  arg-dispatch is inert (blank `--version`) — the known seed-run arg-alias quirk. So
  a FUNCTIONAL interning redeploy needs the full bootstrap flow (GPU runtime bundle
  present so the Stage4 closure passes), not this stripped validation shortcut.
- Net: interning-active proven (fullbuild grep=1); linear parse proven (stage3 to
  412K chars); `bin/release` intentionally left untouched.

## Update 2026-07-25: source-matched Stage3 passes; Stage4 still retains parse state

The warm-cache Stage3 owner-provenance self-host completed with 3 compiled,
676 cached, 0 failed in 67.1s. Its 20 MB bootstrap artifact has SHA-256
`cf4834e6d8b8c5b7b148c4e86cf395f76fd5f665dd8c97bcc2f695a498056ca2`
and passed bootstrap version/error-path sanity.

The canonical Stage4 command was stopped after about 4.7 minutes at only
207/1,155 parsed files because RSS had reached 36,311,984 KiB and
`heap_registry` about 4,485,786. It had emitted no artifact or cache objects.
This confirms the retained parser-state defect on Linux with the latest
source-matched Stage3.

The command-line path also silently ignored the bootstrap script's
`--low-memory` option. The validator, parser, and both `CompileOptions`
construction branches now propagate it, with a focused 13/13 parser contract
pass. That enables the existing phase-boundary evictions, but does not close
this bug: `parse_all_impl` still retains every parsed source/AST until phase 2
ends. The next repair must release per-file parse material while preserving a
cached source fingerprint for correct object-cache invalidation, then pass the
existing multi-file RSS and changed-source cache regressions before one bounded
Stage4 retry.

## Update 2026-07-25: bounded retention repair does not scale to full Stage4

A source-matched rebuild containing short-token interning, shared immutable
empty AST slots, fingerprint-safe source metadata eviction, and fail-closed
native cache setup passed Stage2/Stage3 with 679 compiled and 0 failed.
Stage3 used 324,000 KiB max RSS and produced SHA-256
`01f856054ef6f61a8dae11934d609eb4327ad586f5c7c85877d37720d567c7f1`.
Bootstrap sanity and the 20/40-file guards passed; both guards used
136,888 KiB max RSS. Changed-source output correctly moved from `41` to `42`.

The unchanged-source cache criterion failed: both fixture builds reported
`1 compiled, 0 cached`. The canonical full-CLI Stage4 attempt was terminated
after 7m35s while still in phase 2, at 57,792,476 KiB max RSS and
`heap_registry` about 5,039,086. It emitted no CLI. True per-file phase-2 AST
release and cache-hit admission remain required. Do not repeat this Stage4
command without that repair.

### Corroborating data point 2026-07-25 (independent session; ran the command
### before reading this doc — see caution below)

Same canonical Stage4 command, `--threads 1`, `--low-memory` on, stage3
source-matched and interning-bearing, run in isolation after a competing
bootstrap finished. Extends the curve above to its furthest-observed point:

| t | files parsed | heap_registry | RSS |
|---|---|---|---|
| 9s | phase1 done (n_sources=1550, unique=1151) | 1,616,585 | — |
| 943s | ~1,390 (examples/.../cmm_parser_expr.spl) | 8,049,651 | ~99 GB |
| 966s | ~1,400 (src/os/drivers/real_device_readiness.spl) | 8,312,303 | 100 GB |

Killed manually at 2 GB host free. Consistent with the 57.8 GB / 5.0 M point
above — same monotonic slope, just further along; **no new mechanism**, and it
does NOT contradict any finding here. Confirms only that `--threads 1` does not
help (thread count is not the driver) and that the phase-2 wall is reached even
with no competing build on the host.

**Caution for future sessions (process, not mechanism):** this run should not
have happened — the line directly above it already said so. Two full Stage4
attempts each drove a shared 128 GB host to 1-2 GB free, risking every other
session on the box. Before running the canonical Stage4 command, read this
doc's tail first. If a bounded repeat is genuinely needed, cap it
(`systemd-run --scope -p MemoryMax=40G`, or `ulimit -v`) so the experiment dies
before the host does, instead of relying on someone watching a sampler.

## UPDATE 2026-07-25 (this session): eviction itself is a memory-reclamation
## NO-OP on this runtime, regardless of granularity — confirmed with a
## controlled in-process probe, not inference

This session did not re-run full Stage4 (peak ~111GB confirmed by a fresh
controlled measurement on worktree HEAD `1ddf2a2b87f`, both with interning
present (`grep rt_string_new_literal` = 4) and absent — interning does not
move the peak, matching this doc's own "not the dominant contributor for
Stage4" pattern once you account for full-corpus retention below). Instead of
another full/near-full run, this session isolated and answered the one
question every prior update in this doc left open: **does the existing
`--low-memory` eviction path (`evict_sources()`/`evict_ast()`/`evict_hir()`,
`driver_types.spl:166-187`) actually reduce the live `heap_registry` count
when it runs, independent of whether it runs per-file or per-corpus?**

### Root cause (confirmed by code + a controlled micro-probe)

`evict_sources()` (`driver_types.spl:166-174`) does:
```
me evict_sources():
    var metadata: [SourceFile] = []
    for source in self.sources:
        metadata = metadata.push(SourceFile(path: source.path, content: "", module_name: source.module_name))
    self.sources = metadata
```
`evict_ast()` (line 177-178) is `self.modules = {}`. Both **build a fresh
replacement container and reassign** — they never call any free/unregister
primitive (`rt_string_free`, `rt_array_free`, `unregister_heap_ptr`) on the
discarded old container or its elements. `heap.rs`'s own doc comment (already
cited earlier in this doc) says objects on this tier "stay registered for the
process lifetime" unless something **explicitly** frees them — dropping the
last reference is not enough; this runtime has neither GC nor refcounting.
So by construction, `evict_sources()`/`evict_ast()` cannot reduce RSS or
`heap_registry` no matter where in the pipeline they are called from —
per-file or per-corpus granularity is irrelevant, because neither shape frees
anything.

**Direct proof** (`evict_probe.spl`, self-contained, no driver/CLI
involvement — isolates the eviction *pattern* itself from the rest of the
pipeline): built and run via the existing self-hosted Stage3 binary
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, cranelift,
`core-c-bootstrap`, confirmed interning-bearing via
`strings -a … | grep -c rt_string_new_literal` = 5):
```
before=0 after_fill=10002 after_evict=10004 delta_fill=10002 delta_evict=2
```
Filling an array with 5,000 dynamic strings registers +10,002 heap objects
(≈2/string — array growth + string). Then performing **exactly** the
`evict_sources()` pattern — building a fresh same-shape replacement array and
reassigning over the old one (dropping the last reference to all 5,000
strings and the old array) — adds only **+2** registered objects (the new
container's own allocation) and removes **zero**. The discarded 5,000
strings + old array stay in `heap_registry` (and resident in RSS) forever.
This directly answers the open question the 2026-07-20/24/25 updates above
left unresolved ("why hasn't a fix landed") one level earlier than they were
looking: **even a hypothetically-perfect per-file eviction rewrite would
still show ~0% RSS improvement with today's `evict_*` implementations**,
because the defect is not "eviction runs too late" (granularity) — it's
"eviction never frees" (mechanism). The per-file-granularity fix proposed in
the 2026-07-20 update (and the fingerprint hazard that blocked it — now
independently confirmed MOOT: `native_sources_fingerprint` is computed once
in phase 1 at `driver.spl:332` from the un-evicted `self.ctx.sources` and
cached, then read back by value at `driver_aot_output.spl:331-334` — no
later recompute from possibly-evicted content) is real and worth doing, but
it is not sufficient by itself.

### Why no fix was attempted this session (same reasoning class as 07-20's)

A real fix needs an application-level free primitive that takes a `text`/
`[text]`/`Dict` *value* (not a raw sffi pointer) and safely deep-frees it.
Searched for one: `rt_array_free`/`rt_string_free` externs exist only in
low-level SFFI/codegen-internal contexts (`70.backend/sffi_minimal.spl`
operates on raw `i64` pointers from `rt_file_read_text`-style FFI calls, not
on ordinary `text` values; `rt_array_free` call sites are all inside codegen
backends emitting IR, not callable from driver-tier `.spl`). Building one
requires (a) a safe way to extract a heap pointer from an ordinary `text`/
array `RuntimeValue` at the application level, (b) recursing into element
frees for `[text]` (the existing `rt_array_free` frees only the outer
buffer, per `collections.rs:1438-1454`, cited earlier in this doc), and (c)
resolving the still-open aliasing question from the 2026-07-24 update
("leans ALIASED, not conclusively resolved" — whether `text` assignment
across the arena-getter → converter → `Function`/`Module` boundary copies or
shares the backing buffer). Freeing `source.content` specifically looks safe
under `--low-memory` (the one known post-phase-2 reader, the phase-3 HIR
reparse fallback at `driver.spl:948-957`, is itself gated
`not self.ctx.options.low_memory`), but freeing AST-node text fields is not
proven safe without answering (c) first. Given this doc's own three prior
sessions declined the same patch for the same reason, and the mission's
three-cycle-per-stage budget, this session did not force it either — but the
target is now sharper than before: **add a value-level deep-free primitive
first (scoped to `text` and `[text]`, validated against the alias question),
then re-attempt the per-file `evict_sources()` granularity fix on top of it.
Validate with `evict_probe.spl`-style before/after `heap_registry` deltas
(cheap, no corpus needed) before spending a multi-file or full-Stage4 run.**

Repro artifact: `evict_probe.spl` (reproduces the above numbers in <10s,
no corpus/bootstrap needed) — see session bundle
`stage4_memory_rootcause.md` for the exact source and build command.

## UPDATE 2026-07-25: remove linear string-registry lookup from the parse path

A fresh generation-2 attempt established a second scaling factor. With one
197-character source and about 1,400 registered heap objects, phase 2 parsed in
7ms. After loading the 908-source compiler closure, the first files parsed at
roughly 10–50 seconds each with about 433,000 objects already registered.
`runtime_native.c` validated every tagged string by linearly scanning the entire
string registry, making frequent text operations scale with all prior
allocations.

The existing open-addressed boxed-float registry is now the shared registry for
process-lifetime strings and floats. Membership remains a pointer-only check
before the caller reads the common leading `kind`; registration is locked,
amortized O(1), and allocation failure frees the new object (boxed floats retain
their existing inline fallback). Arrays remain on their deletion-aware registry.

`clang -fsyntax-only` and the focused hosted C runtime contract pass. The
blocking seed-linker defect was also fixed in source: qualified unresolved
symbols now try a unique full-module suffix before any short-name alias, so
`io__env_ops__env_get` resolves to
`nogc_sync_mut__io__env_ops__env_get` even when other modules define
`env_get`. Qualified misses fail closed instead of binding an unrelated leaf.
Focused resolver tests pass. A source-matched generation-1 benchmark still
requires rebuilding the Rust bootstrap seed with that fix; do not credit the
multi-file performance gate or full Stage4 until that rebuild and benchmark
complete.

## UPDATE 2026-08-02: claimed — generated-facade hint scan retains lines for
## every source

- **Claim:** `stage4_perf_profile` owns this narrow fix. Other Stage 4 resolver
  work must not edit `module_surface_export_origin_hints` concurrently.
- **Observed profile:** the legacy Phase-2 trace parsed about 1,198 files in
  148.5 seconds and grew `heap_registry` to 49,245,805. Separate progress
  samples show the pre-streaming process rising monotonically to 19,219,784
  KiB RSS. Current streaming attempts finish the failing boundary in about
  three minutes but still reach roughly 8 GiB RSS and run the parse/surface
  stage primarily on one CPU.
- **Concrete avoidable allocation:**
  `module_surface_export_origin_hints` calls `source.content.split("\\n")`
  for every parsed source. On the no-GC self-hosted runtime the resulting line
  texts remain registered even though only files containing the exact
  `# Re-exported from ` marker can produce an origin hint.
- **Corpus discriminator:** 11,200 of 11,510 `.spl` files under the Stage-4
  source roots do not contain the marker; those files total 79,498,687 of
  80,263,679 bytes. More directly, among the 1,197 files completed by the
  retained Phase-2 trace, only 8 files / 89,214 bytes contain the marker; the
  fast path avoids splitting 1,189 files / 16,346,111 bytes. They can return
  an empty hint dictionary before splitting without changing provenance
  behavior.
- **Fix/acceptance:** guard the split with an exact marker `contains` check;
  retain generated-facade and explanatory-suffix behavior; add a source-order
  regression that fails if the split moves ahead of the guard. This is one
  bounded contributor, not a claim that transient string ownership or the
  remaining Stage-4 peak is solved.

## UPDATE 2026-08-06: `evict_mir_module()` investigated for a bounded free —
## NOT fixable at the driver tier. The blocker is NOT the aliasing question the
## three prior declines named; it is that the C runtime has **no dict-free and
## no object-free primitive at all**. Four independent aliases found on top.
## STATIC ANALYSIS ONLY — nothing in this update was build-measured.

**Honesty header.** No code landed in this update. Nothing below was measured
on a running build: the machine was carrying a live 50+ GB T3 `native-build`
retry and this session was scoped to micro-probes only, which cannot exercise
the driver. Every claim below is source-level and carries a `file:line`. The
one prior *measured* result this relies on is the 2026-07-25 `evict_probe.spl`
run already recorded above (`delta_evict=2`, zero reclaimed).

### Correction to the 2026-07-25 decline: the primitive it asked for now EXISTS

The 2026-07-25 update closed with "**add a value-level deep-free primitive
first (scoped to `text` and `[text]`…), then re-attempt**". That primitive was
subsequently built and is committed:

- `rt_array_free_deep(int64_t value) -> int64_t` — `src/runtime/runtime_native.c:5335`,
  declared `src/runtime/runtime.h:372`.
- It is exactly what was asked for: takes a tagged **value**, not a raw sffi
  pointer; recurses into elements; all-or-nothing (refuses and frees *nothing*
  rather than half-freeing, `runtime_native.c:5172-5187`); keeps a `seen`
  pointer set so an internal alias or cycle refuses the whole call
  (`:5215-5219`); same refuse-biased contract as `rt_string_free`.

Two things keep it from being usable today, and they are separately fixable:

1. **It is unreachable from `.spl`.** No `extern fn rt_array_free_deep` is
   declared anywhere in `src/` (grep over `--include=*.spl` returns zero).
   It is also absent from the deployed self-hosted binary — `nm -a` and
   `strings -a` on `bin/release/x86_64-unknown-linux-gnu/simple` both return
   **0** matches, i.e. it is currently dead code that no lane links.
2. **No Rust-runtime twin.** `grep -rn rt_array_free_deep src/compiler_rust/`
   returns nothing. `rt_string_free` has twins in both runtimes by design
   (`collections.rs:1814` names itself the "Rust-side twin of `rt_string_free`
   in `src/runtime/runtime_native.c`"). Any `.spl` caller added today would
   link on the C-runtime native lane and fail to resolve on the seed/JIT lane.

### The actual blocker for `evict_ast` / `evict_hir` / `evict_mir_module`

Complete inventory of value-level free primitives in the C runtime that the
self-hosted binary links (`runtime_compiler.spl:284` builds `runtime_native`
into the archive; `stage4_symbol_closure.spl:178`):

| primitive | shape | site |
|---|---|---|
| `rt_string_free` | one string, registry-checked, refuses `SHARED` | `runtime_native.c:5418` |
| `rt_array_free` | array, **shallow** — strands every heap element | `runtime_native.c:5151` |
| `rt_array_free_deep` | array, deep, all-or-nothing | `runtime_native.c:5335` |

**There is no `rt_dict_free`, no `rt_object_free`, no `rt_tuple_free` in the C
runtime.** (The Rust runtime has `rt_dict_free`/`rt_object_free`/`rt_tuple_free`
— `dict.rs:134`, `objects.rs:159`, `collections.rs:1901` — but the Rust runtime
is not what the self-hosted binary links, so that does not help.)

Now compare against what the three evict targets actually hold:

- `CompileContext.modules`, `.hir_modules`, `.mir_modules` are all
  `Dict<text, …Module>` (`driver_types.spl:159-164`).
- `MirModule` (`50.mir/mir_instruction_graph.spl:357-364`) is **four Dicts of
  struct objects**: `functions: Dict<SymbolId, MirFunction>`, `statics`,
  `constants`, `types`.
- `MirFunction` (`:159-206`) owns `locals: [MirLocal]`, `blocks: [MirBlock]`
  (arrays **of objects**), `type_bindings: Dict<text, HirType>`, and ~15 text
  fields.
- `SymbolId` is a struct wrapping an `i64` (`20.hir/hir_types.spl:71-73`), so
  even the dict *keys* are heap objects.

Every level is a Dict or an array-of-objects. `rt_array_free_deep` refuses any
element that is not a registered non-shared string or a registered array
(`runtime_native.c:5203-5214` explicitly lists dicts and enums/closures as
refusals, with the reasoning that freeing the buffer would *strand* them).
`rt_array_free` would free the `[MirBlock]` buffer and strand every block —
the irreversible leak `runtime_native.c:5178-5185` argues against by name.

So the conclusion is sharper than "non-trivial runtime work": **no sequence of
driver-tier `.spl` calls over today's primitive set can reclaim a MirModule,
an HirModule, or an AST module. The gap is a missing dict-free and object-free
in `runtime_native.c`, not a missing proof about aliasing.** That is why this
session did not force a patch either — but the next session no longer has to
re-derive *what* to build.

### Four aliases that must be resolved even after the primitives exist

These were found while checking whether MIR-after-codegen is provably unshared.
It is not. Ranked:

1. **`ctx.bootstrap_entry_mir` aliases `ctx.mir_modules[entry]`, and
   `evict_mir_module` does not clear it.** Every lowering branch stores the
   *same* value into both — `driver_pipeline_lowering.spl:163-165`, `:238-240`,
   `:269-271`, `:284-286`; `driver_bootstrap.spl:139-140`, `:181-182`.
   `evict_mir_module` (`driver_types.spl:231-232`) is only
   `self.mir_modules.remove(name)`, whereas `evict_hir` (`:226-228`) *does*
   clear `bootstrap_entry_hir`. The alias is read back at
   `driver_aot_native_output.spl:587-590`. **This asymmetry is a latent bug
   today even without any free** and is the first thing to fix.
2. **`_bootstrap_mir_functions: [MirFunction]`** — a module-level global
   (`50.mir/_MirLowering/bootstrap_globals.spl:113`, pushed `:218`, read
   `:418-421`, reset only `:175`) retains `MirFunction` values past codegen on
   the bootstrap/flat lane.
3. **`output_format == both` + `--low-memory` silently loses SMF output.**
   `driver_aot_pipeline.spl:143-149` runs `compile_to_native` then
   `compile_to_smf`, but `driver_aot_smf_output.spl:111-115` and `:131`
   re-iterate `ctx.mir_modules` after `driver_aot_native_output.spl:338`/`:426`
   already evicted them. Another latent bug independent of freeing.
4. **`MirFunction.name` / `export_name` are the *same heap strings* as HIR/AST
   and the SymbolTable.** `50.mir/_MirLowering/function_lowering.spl:132`
   assigns `fn_.name` directly; `HirSymbol.name` (`hir_types.spl:82-85`) shares
   that lineage. Per-function `rt_string_free` on names would dangle the symbol
   table. (Only method/static names get a fresh string, `:138-139`.)

What is *not* a hazard, checked and cleared: no `.smf` template store holds
MIR (the SMF linker works on serialized bytes — `smf_reader.spl:259/321/422`,
`lazy_instantiator.spl:196`; `jit_context.spl:15` holds `TemplateBytes`);
monomorphization caches store text/i64 ids only (`core/type_erasure.spl:16-18`,
`monomorphize.spl:17`); codegen takes one module at a time with no cross-module
MIR reads (`driver_aot_native_output.spl:594-596`); and `ParallelBuilder` is
**not** actually threaded — `build()` runs `compile_fn` inline in a `while`
loop in both branches (`driver_build/parallel.spl:300-326`, `:344-395`), so
there is no cross-thread MIR sharing to reason about.

One more aliasing *producer* worth recording: `driver_pipeline_aop.spl:111` and
`:126-127` re-wrap modules with `ctx.mir_modules[name] = MirModule(...)` /
`inject_debug_trace(...)`, reusing the inner dict handles. Struct values are
handles at runtime, not copies — `llvm_lib_type_mapper.spl:41-50` maps
`MirTypeKind.Struct` to `ptr_type()`, and `rt_dict_get` returns the bare
`int64_t` handle (`runtime_native.c:6895`). So the old wrapper leaks and the
new one aliases its innards.

### Ordered plan to unblock (each step independently landable + probe-testable)

1. Fix hazard 1 and hazard 3 above. Both are latent bugs today, both are
   small, and neither needs any new runtime primitive.
2. Add the Rust-runtime twin of `rt_array_free_deep` (mirror
   `collections.rs:1814`'s twin convention) so both lanes resolve the symbol.
3. Declare `extern fn rt_array_free_deep` in `.spl` beside `rt_string_free`
   (`driver_types.spl:28`) **together with its first real caller** — an unused
   extern is dead code. Verify with an `evict_probe.spl`-style
   `heap_registry` before/after delta (<10s, no corpus).
4. Only then add `rt_dict_free` + `rt_object_free`/`rt_free_deep` to
   `runtime_native.c` under the same refuse-biased, all-or-nothing contract
   `rt_array_free_deep` already establishes. This is the step that actually
   unblocks `evict_ast`/`evict_hir`/`evict_mir_module`, and it is the one that
   needs a runtime rebuild, so it should be scheduled when the machine is not
   carrying a bootstrap.

Note for whoever picks this up: `src/runtime/runtime_native.c` was dirty in the
shared working copy during this session (another lane is mid-flight on it), so
it was deliberately not edited here.

### Still true, unchanged

`reclaim_source_contents()` (`driver_types.spl:198-204`) is real reclamation
and is wired in at `driver_orchestration.spl:132-134` and
`driver_hir_pipeline_lowering.spl:161-163`. The 2026-08-02 facade-hint guard
landed (`20.hir/hir_lowering/module_surface.spl:818`). Neither is affected by
anything above.

## UPDATE 2026-08-06 (later, second session): steps 1-3 of the ordered plan
## LANDED and test-verified. Step 4 (`rt_dict_free`/`rt_object_free`) is still
## OPEN and still blocked on `runtime_native.c` being another lane's live file.

This continues the ordered plan at the end of the previous update and does
**steps 1, 2 and 3 only**. It deliberately does not touch
`src/runtime/runtime_native.c` or `src/runtime/runtime.h`: both were checked at
the start AND at the end of this session and `runtime_native.c` was **still
dirty** in the shared working copy, i.e. another lane is still mid-flight on it.
See "Step 4 status" at the bottom.

Unlike the previous update, everything below was **executed**, not reasoned. The
verification method for each claim is stated inline: `measured` means a number
was read out of a run, `reasoned` means it follows from source that was read.

### Step 1 -- hazard 1 and hazard 3, fixed with regression specs

**Hazard 1: `evict_mir_module` left `bootstrap_entry_mir` dangling.**

The previous update proposed matching on the evicted name. That is not
sufficient on its own, and the reason is worth recording: the alias cannot be
recognised by comparing `MirModule.name`, because the bootstrap flat lane builds
`MirModule(name: "", ...)` (`50.mir/_MirLowering/bootstrap_globals.spl:784`) and
stores it under a real key. The name in the dict and the name in the struct are
not the same thing.

So `CompileContext` gained one field, `bootstrap_entry_mir_name: text`
(`driver_types.spl`), recording the key the alias was registered under, plus a
`set_bootstrap_entry_mir(name, module)` setter used by every site that writes
BOTH the dict and the alias:

- `driver_pipeline_lowering.spl` -- all four branches (skip-lower, bootstrap
  fixed-entry, `--entry-closure` direct, HIR-map fallback).
- `driver_bootstrap.spl` -- the flat closure path and the globals path.

`driver_pipeline_lowering.spl`'s `SIMPLE_BOOTSTRAP` branch and
`driver_bootstrap.spl:498` were deliberately left alone: they set the alias
WITHOUT inserting into `mir_modules`, so there is no dict entry whose eviction
could invalidate them, and registering a key there would let an unrelated
eviction clear a live alias.

`evict_mir_module` now clears the alias when, and only when, the evicted name is
the registered entry key -- mirroring `evict_hir`, which already cleared
`bootstrap_entry_hir`.

**Hazard 3: `both` + `--low-memory` silently lost SMF output.**

Fixed at the decision point rather than at the eviction sites, so it is
testable: `driver_mir_eviction_enabled(low_memory, format)` in
`00.common/driver_core_modes.spl` returns `low_memory and not is_both(format)`,
and `driver_aot_native_output.spl` computes its `low_memory` local from it.
Both eviction call sites (`:338` cache-hit and `:426` post-compile) read that
one local, so a future third call site cannot miss the rule. Skipping eviction
was chosen over reordering the phases or hard-erroring: it is the smallest
change, it needs no new failure mode, and `both` is by construction the format
that cannot afford to drop MIR. Eviction is an optimisation; correct output is
not.

**Regression spec** (`measured`):
`test/01_unit/compiler/driver/mir_eviction_hazards_spec.spl` -- 7 examples,
7 passed. Sabotage-checked: with the two fixes reverted in place the run is
`7 examples, 2 failures`, failing exactly "clears the bootstrap entry alias when
the entry module is evicted" and "disables MIR eviction under --output-format
both"; restoring them returns 7/7. The spec also pins the two directions a naive
fix gets wrong -- evicting a DIFFERENT module must NOT clear the alias, and
`--low-memory` must still evict for `native`/`smf`/`self-contained`.

Note for anyone extending that spec: `CompileOptions` must be imported from its
defining module `compiler.common.driver_compile_options`, not through the
`driver_core_types` facade. Through the facade, `CompileContext.create` dies
with ``class `CompileOptions` has no field named `mode` `` -- a module-resolution
defect, not a missing field.

### Step 2 -- the Rust twin of `rt_array_free_deep`

`rt_array_free_deep` now exists in
`src/compiler_rust/runtime/src/value/collections.rs`, beside `rt_array_free` /
`rt_string_free`, exported from `value/mod.rs`. It matches the C contract at
`runtime_native.c:5335` clause for clause: two-phase, read-only classify then
commit; all-or-nothing (a refusal frees NOTHING); byte-/u64-packed payloads skip
the element scan; immediates are leaves; non-shared registered strings and
registered arrays recurse; everything else -- dicts, tuples, objects, closures,
enums, foreign pointers, already-freed pointers, and raw i64s that merely alias
the heap tag -- refuses the whole call. A `seen` pointer set refuses on any
internal alias or cycle, proving the reachable structure is a tree. It reuses
the existing registry helpers (`get_typed_ptr_mut`,
`unregister_heap_ptr_checked`) rather than reinventing membership tests; every
dereference is gated on registry membership, which is what makes a tag-aliasing
i64 safe.

**Verification** (`measured`): nine contract tests in
`mod array_free_deep_contract_tests` in that file -- 9 passed. Every case reads
`rt_heap_registry_count()` before and after and asserts on the DELTA, because a
verdict of 1 that did not shrink the registry would be the primitive lying.
Sabotage-checked: turning the catch-all `Refuse` into `Leaf` fails 7 of the 9.
The full `cargo test -p simple-runtime --lib` run has 7 pre-existing failures
(executor threads, loader package format, native lib manager, dict invalid
value, low-heap tagged values, heap attribution); the identical 7 fail with this
module skipped, so none are caused by this change.

### Step 3 -- reachable from `.spl`, with a caller

The previous update was right that the extern was the gap, but understated it:
declaring `extern fn rt_array_free_deep` is NOT enough to make it callable. The
symbol has to be registered in four more places or the compiler rejects the
declaration outright with `semantic: unknown extern function:
rt_array_free_deep` -- which is exactly how the new spec failed on its first
run, before any assertion executed. Landed:

- `.spl` extern + wrapper: `70.backend/sffi_minimal.spl`, beside `rt_string_free`.
- Interpreter dispatch: `interpreter_extern/sffi_array.rs`
  (`rt_array_free_deep_fn`) + `interpreter_extern/mod.rs`.
- Cranelift/JIT ABI: `codegen/runtime_sffi.rs` (`&[I64] -> &[I64]`, NOT
  `rt_array_free`'s void shape) and `elf_utils.rs` symbol resolution.
- LLVM declares, all three emitters that special-case `rt_string_free`:
  `llvm_backend.spl`, `llvm_lib_translate.spl`,
  `_MirToLlvm/asm_constraints_helpers.spl`, plus the Cranelift adapter's
  i64-returning branch in `cranelift_codegen_adapter.spl` -- taking the
  `rt_array_free` void branch there would have discarded the all-or-nothing
  verdict the caller must read.

**No production call site was added, deliberately.** Every array-shaped
candidate in the driver fails the same aliasing bar the rest of this
investigation applies: `uncached_names` / `object_files` (`[text]`) hold the
SAME text values as the `mir_modules` dict keys, so freeing them would free
strings the dict still owns -- and `rt_array_free_deep` cannot detect an alias
from OUTSIDE the structure, so it would accept the call and corrupt the keys.
`collect_smf_bytes`'s `[u8]` accumulator is genuinely large and genuinely
garbage after each `concat`, but arrays are value types here and each
intermediate is reachable from the previous binding, so unsharedness is not
provable by reading the source. Forcing a call site through that bar to avoid a
"dead extern" would have been the exact cover-up this bug file exists to prevent.
The extern therefore lands with a **regression spec as its caller**, which the
previous update's own step 3 allows for.

**Verification** (`measured`, two ways):

1. `test/01_unit/runtime/array_free_deep_spec.spl` -- 6 examples, 6 passed. It
   asserts only what is true on EVERY lane (reachability, strict binary verdict,
   never grows the registry, second free refuses, and the implication
   `verdict == 1` => the registry dropped by at least `elements + 1`). It does
   NOT assert an unconditional reclaim, and the file says why: on the
   interpreter lane an array is `Value::Array`, a Rust Vec with no runtime heap
   object behind it, so the honest verdict there is 0 and an unconditional
   assertion would pass or fail on which lane ran rather than on correctness.
2. An `evict_probe.spl`-style `heap_registry` delta, run directly (<1s, no
   corpus). 2000 unique dynamically-built strings in a `[text]`:

   | lane | `delta_fill` | `verdict` | `delta_free` |
   |---|---|---|---|
   | JIT (default) | 4249 | **1** | **2001** |
   | `SIMPLE_EXECUTION_MODE=interpret` | 0 | 0 | 0 |

   2001 = 2000 element strings + 1 array header, i.e. the deep free reclaimed
   the elements the shallow `rt_array_free` would have stranded. The interpret
   row registering nothing at all is the direct confirmation of the lane
   reasoning above.

   Reproduce: build a `[text]`, read `rt_heap_registry_count()` before/after,
   call `rt_array_free_deep`, and run it with the REBUILT seed
   (`src/compiler_rust/target/debug/simple`). Running it through the deployed
   `bin/simple` instead reports `verdict=0` and `unknown extern function` --
   the deployed binary predates this change. That is the usual
   binary-provenance trap, not a defect in the primitive.

### Step 4 status: still OPEN, still out of scope

`rt_dict_free` + `rt_object_free`/`rt_free_deep` in `runtime_native.c` remain
unwritten, and they are still the step that actually unblocks `evict_ast` /
`evict_hir` / `evict_mir_module`. Nothing above changes that: hazards 1 and 3
were latent correctness bugs, and `rt_array_free_deep` cannot touch a
`Dict<text, MirModule>`.

`git status src/runtime/runtime_native.c` was re-checked after this session's
work and still reports ` M` -- the other lane's edits are still uncommitted, so
step 4 is **not yet unblocked**. Whoever picks it up should re-check that status
first; when it comes back clean, step 4 can proceed against the same
refuse-biased, all-or-nothing contract, and the Rust twin now landed here is the
template for the matching Rust side it will also need.

Hazards 2 (`_bootstrap_mir_functions` retaining `MirFunction`s past codegen) and
4 (`MirFunction.name` sharing heap strings with HIR/AST and the SymbolTable) are
untouched and remain as described in the previous update.

## UPDATE 2026-08-06 (third session): step 4's C primitives now EXIST, and the
## driver eviction path STILL CANNOT USE THEM. Wiring one
## up would reclaim ~0.1% of the target memory while introducing a
## use-after-free. MEASURED, not reasoned: `src/runtime/test/
## rt_driver_eviction_reclaim_selfcheck.c`.

`92b09df4583` landed `rt_dict_free_deep` and `rt_free_deep` in the C runtime,
closing the "no dict-free primitive at all" half of the previous update's
blocker. Their refusal discipline was re-verified against the step-2/3 contract
and is intact: one shared planner with `rt_array_free_deep`
(`runtime_native.c:5364`), one `seen` set spanning every kind, keys classified
exactly like values (`:5416`), only `occupied==1` slots followed, and
`rt_core_deep_free_classify` (`:5331`) gating every dereference on registry
membership with a catch-all `REFUSE`.

So the primitives are correct. The driver still cannot call them, for a reason
the earlier updates had not isolated.

### The measurement

All four numbers below come from one probe built against the real C runtime
(build line in the file's header comment; it links `src/runtime/*.c`, not a
mock). N=1000 entries.

| probe | shape | verdict | delta_free |
|-------|-------|---------|------------|
| P0 RED | `self.modules = {}` (today's eviction) | n/a | **0** of 2001 |
| P1 | `Dict<text, text>` | 1 | **2001** |
| P2 | `Dict<text, class instance>` | **1** | **1001** of 2001 |
| P3 | keys aliased from OUTSIDE | **1** | frees a live alias |
| P4 | `rt_free_deep(class instance)` | 0 | refuses |

**P0 confirms the RED.** `evict_ast()` / `evict_hir()` / `evict_mir_module()`
reclaim exactly **0** of 2001 allocations. With no GC and no refcounting,
dropping the reference is a pure no-op, as this bug has assumed throughout. The
replacement `{}` costs one *additional* registration, so eviction today is very
slightly net-negative.

**P1 confirms the primitive works**, at exactly the rigor step 2 set:
`verdict=1, delta_free=2001` = 1000 keys + 1000 values + the dict header.

**P2 is the finding.** The driver's three eviction targets are, without
exception, `Dict<text, CLASS INSTANCE>`:

- `driver_types.spl:66`  `modules: Dict<text, ParserModule>`
- `driver_types.spl:68`  `hir_modules: Dict<text, HirModule>`
- `driver_types.spl:70`  `mir_modules: Dict<text, MirModule>`

On this lane a class/struct instance is an **untagged, unregistered,
header-less `rt_alloc` block** — `runtime.h` says so in `rt_free_deep`'s own
contract comment: "not identifiable at runtime at all". `rt_free_deep` therefore
correctly refuses one as a ROOT (P4, verdict=0).

But in ELEMENT position the same pointer takes a different path.
`rt_core_deep_free_classify` tests `(raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP`
and returns `LEAF`. A malloc block is 16-aligned, so `raw & 7 == 0 ==
RT_VALUE_TAG_INT` — **byte-for-byte indistinguishable from a tagged immediate.**
The classifier cannot refuse what it cannot see, so it classifies every
`ParserModule` / `HirModule` / `MirModule` as a leaf and the call **ACCEPTS**.

The result is the worst available combination:

- `verdict=1` — the caller is told the whole structure was reclaimed.
- `delta_free=1001` — only the 1000 key strings and the dict header came back.
- The 1000 class instances, **which hold essentially all of the memory this bug
  is about** (every AST/HIR/MIR node hangs off them), are silently STRANDED.

The all-or-nothing contract is not violated — it is satisfied vacuously, because
the planner never learns there was anything else to free. This is not a bug in
`rt_dict_free_deep`; it is the ceiling of what any deep-free can do on a lane
where the objects carrying the memory are unidentifiable.

**P3 confirms hazard 4 empirically, and it is worse than "it refuses."** The
`seen` set only spans nodes the planner TRAVERSES, so an alias held from OUTSIDE
the structure is undetectable by construction. `MirFunction.name` /
`export_name` are the same heap strings as the HIR/AST/SymbolTable copies, which
live outside `mir_modules`; hazard 2's `_bootstrap_mir_functions` global is the
same story. The probe's externally-held key survives the call as a dangling
pointer: `verdict=1`, and the outside holder now names freed storage. Step 2
predicted exactly this for arrays ("cannot detect an alias from OUTSIDE the
structure, so it would accept the call and corrupt the keys"); it is now
measured for dicts.

### Conclusion: step 4 is landed at the runtime tier and BLOCKED at the driver tier

No call site was added to `driver_types.spl`. Adding one would, per the numbers
above, reclaim ~1001 of 2001 registrations — **none of them the module objects**
— while freeing key strings that HIR, the AST and the SymbolTable still point
at. That trades a no-op for a use-after-free and buys ~0.1% of the target
memory. A refusing free that reclaims nothing is not a fix; an ACCEPTING free
that reclaims the wrong 0.1% and corrupts the rest is strictly worse than the
no-op it replaces.

There is no sabotage check to report because there is no GREEN: P1 vs P2 is the
discriminating control — same harness, same N, only the value shape differs, and
that alone moves `delta_free` from 2001 to 1001.

### What would actually unblock it (in order)

1. **Make class instances identifiable.** Until a `ParserModule`/`HirModule`/
   `MirModule` can be recognised at runtime, no deep-free can reach the memory.
   This is a codegen/representation change (a header or a registry for
   class allocations), not a driver or runtime-primitive change. It is the ONLY
   step that changes the P2 number.
2. **Resolve hazards 2 and 4 first anyway** — they are prerequisites, not
   side-quests. Even with identifiable objects, P3 shows the planner cannot see
   an external alias, so `_bootstrap_mir_functions` must be cleared and
   `MirFunction.name` must own its strings (or the strings must be interned and
   thus refused) BEFORE any call site is added.
3. Only then is a `driver_types.spl` call site measurable.

Hazards 2 and 4 remain UNRESOLVED. Steps 1-3 remain landed. Step 4's C runtime
primitives are landed (`92b09df4583`); step 4's *driver call site* is now
understood to be blocked on the object-identifiability gap above, which is a
new, separately-trackable item and NOT something the driver tier can fix.

### State-of-the-tree note for whoever picks this up

The multi-registry `.spl`/Rust wiring that would make `rt_dict_free_deep` and
`rt_free_deep` *callable from Simple* (interpreter dispatch table, Cranelift ABI
spec table, ELF symbol resolution, the three LLVM emitters + Cranelift adapter,
and the Rust twin in `value/collections.rs`) exists in the shared working copy
as ANOTHER LANE'S UNCOMMITTED WORK and is **not at `origin/main`** as of this
update — verified by `git grep rt_dict_free_deep origin/main`, which finds only
this document. That wiring is deliberately NOT included in this commit; it is
not this session's to land.

This does not affect any conclusion above. Every number in the table was
measured against the **C runtime directly**, which is what the self-hosted
binary links, so the probe is independent of whether the `.spl` bridge has
landed. It does mean that a future session should not assume the extern is
callable from `.spl` without re-checking `origin/main` first.

## UPDATE 2026-08-06 (fourth session): hazard 4 FIXED as a USE-AFTER-FREE
## correctness bug — NOT as a memory win. Hazard 2 investigated and DECLINED
## with a reason. Eviction is STILL blocked and this update does not change the
## ~65GB peak.

**Scope honesty, stated first.** This session did not unblock eviction and does
not claim to. Per `94b77d8007c` (sibling lane, measured), the real unblock is
making class instances runtime-identifiable — a codegen/representation change.
Hazards 2 and 4 are prerequisites, not the fix. Fixing hazard 4 reclaims **zero
bytes**; it is landed purely because shared name strings are a live
use-after-free hazard that the runtime cannot detect.

**Correction to this file's own earlier framing.** Previous updates leaned on
`rt_array_free_deep` being refuse-biased, and treated "it would refuse on the
alias" as the reason eviction is a no-op. That safety net **does not exist for
these shapes**, and this session reproduced it firsthand rather than taking it
on report:

- The `seen` set spans only the nodes the traversal visits. An alias held from
  OUTSIDE the freed structure — which is exactly the MIR-name <-> HIR / AST /
  SymbolTable case, and exactly the `_bootstrap_mir_functions` case — is
  **undetectable by construction**.
- Measured: an array containing a string that is still live in the caller's
  frame frees with **verdict=1** (ACCEPTED, reported as success), and the
  caller's surviving handle then reads `.len() == -1`. Probe:
  `external_alias_probe.spl`, seed `src/compiler_rust/target/debug/simple`.
- The sibling lane's matching result: class instances come from `rt_alloc`
  (`aggregate_intrinsics.spl:107` -> `runtime_native.c:4756`), a bare `malloc`
  pointer with no tag and no registry entry, so
  `rt_core_deep_free_classify` (`runtime_native.c:5331`) returns **LEAF, not
  REFUSE** — the free accepts and silently strands the objects. See
  `src/runtime/test/rt_driver_eviction_reclaim_selfcheck.c`.

So the correct reading of hazard 4 is inverted from the original entry: it is
not "a reason the deep-free refuses", it is "a silent use-after-free of a
SymbolTable string the moment any MIR deep-free is wired up". That raises its
stakes and it is why it is fixed here even though it saves nothing.

`MirFunction` has ~15 text fields and this update makes only **two** of them
MIR-owned; the other thirteen still alias and are still latent UAF.

### The alias oracle (this is what made RED->GREEN possible at all)

`rt_array_free_deep` keeps a `seen` pointer set and refuses the WHOLE call when
two elements are the same heap pointer (`runtime_native.c:5215-5219`). That
turns it into a pointer-identity test on `text`:

    rt_array_free_deep([a, b]) == 1  =>  a and b are DISTINCT heap strings
    rt_array_free_deep([a, b]) == 0  =>  they ALIAS ... or the oracle is dead

This is a pointer-identity test ONLY for two handles placed in the SAME array.
It is NOT a safety net for a real free — see the correction above: an alias held
outside the traversed structure is accepted, not refused.

The "oracle is dead" clause is not theoretical. **Two separate dead-oracle modes
were hit in this session**, and either one would have faked a RED:

1. The deployed `bin/simple` predates the extern and answers 0 for everything
   (already recorded in the previous update).
2. **Driving the real `MirLowering` in-process forces a JIT bail to the
   interpreter**, where an array is a Rust `Vec` with no runtime heap object, so
   *every* call returns 0 — including the distinct-string control. Measured:
   `MirLowering.new` fails Cranelift codegen with `unresolved constructor call
   'MirLowering.new'`, the run falls back to the interpreter, and
   `control_distinct` reads **0**. An end-to-end probe that lowered real source
   and reported "verdict=0, aliased" would have been reporting the lane, not the
   compiler.

Consequence: every verdict below is gated on a positive control (two
dynamically-built distinct strings must read 1) in the SAME process, and the
spec models the struct-FIELD shape of the lowering site rather than calling it.
The field shape is what the aliasing depends on, and it is reachable on the JIT
lane where the oracle is live.

### Hazard 4 — FIXED

Two sites in `src/compiler/50.mir/_MirLowering/function_lowering.spl`:

- `:132` `var mir_fn_name = fn_.name` -> `fn_.name + ""`
- `:408` `fn_result.export_name = ea.export_name` -> `ea.export_name + ""`

**RED->GREEN, measured**, one process, seed `src/compiler_rust/target/debug/simple`:

| case | verdict | reading |
|---|---|---|
| control: two distinct heap strings | **1** | oracle is LIVE |
| control: same handle twice | **0** | oracle detects aliasing |
| RED — pre-fix `= fn_.name` shape | **0** | MIR name ALIASES the HIR string |
| RED — pre-fix `= ea.export_name` shape | **0** | same for export_name |
| GREEN — landed `+ ""` shape | **1** | MIR owns its name |
| GREEN — landed export_name shape | **1** | MIR owns its export_name |

The sabotage check is structural rather than a source revert: the pre-fix and
post-fix shapes are both present as `lower_aliasing` / `lower_owning` in the
regression spec and execute in the same run against the same live oracle, so
the RED cannot silently stop being red.

**Why `+ ""` and not interpolation.** `"{s}"` on a whole string does NOT
allocate — measured verdict **0**, i.e. it returns the same handle and would
have silently reintroduced the hazard. `s + ""` and `s.replace("::", ".")` both
read **1**. The `.replace` result also retroactively confirms the previous
update's claim that the method/static path (`:139`) was never part of hazard 4,
including when the pattern does not match.

**Measured cost.** One extra string copy per lowered function (two when
`@export("C")`). Upper bound over the whole tree: 117,610 `fn` declarations in
`src/`, mean name length 16.9 bytes = ~1.99 MB of names, ~5.7 MB with per-string
heap headers. Against the ~65 GB peak that is ~0.01%. The tradeoff is not close.

**Regression spec**: `test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl`.
Its header states in those terms that it guards a use-after-free and not RSS.
Every assertion is an implication gated on the positive control, the same
lane-honesty convention `test/01_unit/runtime/array_free_deep_spec.spl` already
established — an unconditional assertion here would pass or fail on which lane
ran rather than on correctness.

### Hazard 2 — investigated, DECLINED, with the reason

`_bootstrap_mir_functions` (`50.mir/_MirLowering/bootstrap_globals.spl:113`)
**is genuinely load-bearing** and cannot be scoped to the lowering state:

- The LLVM object emitter iterates the FLAT accumulator BY INDEX, across module
  boundaries — `70.backend/backend/_MirToLlvm/core_codegen.spl:351/397`, plus
  `aggregate_intrinsics.spl`, `asm_constraints_helpers.spl` and `class_def.spl`,
  which all import `bootstrap_mir_function_count/at/name_at`.
- The entry module lowers first and every `--entry-closure` module APPENDS to
  the same accumulator (`bootstrap_globals.spl:792` docstring). That docstring
  records that NOT appending is what previously produced "undefined symbol" for
  cross-module closure calls (bug
  `bootstrap_stage2_empty_mir_bodies_2026-07-05`).
- So "store names/ids instead of `MirFunction` references" fails outright: the
  emitter needs the actual function to emit a body.

The only remaining shape is release-after-last-consumer. **That is declined, and
the reason is the hazard-3 shape this file already burned a session on:**
`driver_bootstrap.spl:432` re-reads `bootstrap_mir_function_count() > 0` not as
a diagnostic but as the *branch selector* between the real-LLVM emitter, the
`ctx.bootstrap_entry_mir` path, and the stub fallback. A release inside
`bootstrap_emit_real_llvm_object` would make any second call to
`bootstrap_compile_to_native` — `--output-format both` being the obvious one,
the same format that caused hazard 3 — silently take the stub branch. That is a
correctness regression traded for zero measured bytes.

"Zero measured bytes" is the second reason, and it is independent of the first:
there is no GC and no refcounting, so clearing the accumulator drops
*reachability* only. And per `94b77d8007c` a `rt_free_deep` per `MirFunction`
would not reclaim either — it would ACCEPT and strand the class instances. The
global's aliases are likewise invisible to the planner, so hazard 2 is a latent
use-after-free of the same family as hazard 4, just one nobody can currently
trigger because no MIR free is wired.

**What would make hazard 2 landable**, for whoever picks it up: give the release
its own explicit flag so the branch selector at `driver_bootstrap.spl:432` stops
being derived from the accumulator length (mirroring how hazard 1 was fixed by
recording `bootstrap_entry_mir_name` rather than inferring the alias), THEN
release after the last consumer, and gate it through
`driver_mir_eviction_enabled()` so the `both` rule is enforced in one place.
Do that only once a `MirFunction` deep-free can actually reclaim, or it buys
nothing.

### Status after this update

- Hazard 1: fixed (previous session).
- Hazard 2: **open, declined with reason** — see above.
- Hazard 3: fixed (previous session).
- Hazard 4: **fixed for `name` and `export_name` as a use-after-free fix; the
  other ~13 text fields of `MirFunction` are untouched and still alias.**
- What actually gates eviction is NOT this update and NOT step 4's primitives:
  it is making class instances runtime-identifiable so the deep-free planner can
  see them (`94b77d8007c`). The ~65 GB peak is unchanged by this update.
