# Stage-4 self-host full-CLI build: parse-phase memory blowup (~160MB/file, killed at 64GB)

- **ID:** bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20
- **Status:** OPEN
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
