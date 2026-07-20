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
## binary; two leading hypotheses tested and REFUTED with direct evidence; the
## surviving, evidence-backed lead is a per-file O(n²) lexer/parser cost, not a
## classic retention leak. No validated in-tree fix landed — see "why no fix
## shipped" below.

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
### lexer/parser cost, not a classic retention leak
This is a genuinely different mechanism than "AST held live too long" and
matches a pre-existing, independently-noted landmine
(`feedback`/project memory: "Lexer O(n²) parse perf ... char_at re-fetches
whole source + O(n) slice per peek").

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
- **Memory:** since a single file's *own* transient parse cost is
  ~O(file_size) and is not, by itself, unbounded, the multi-file 64GB crash
  is most consistent with **heap fragmentation / high-water-mark RSS from
  the O(n²) allocation churn**, not live-object retention: each file's parse
  makes a very large number of small-to-large transient allocations (from
  the repeated slicing), and even if all of them are correctly freed back to
  this runtime's allocator between files (consistent with finding #1 above —
  the tracked arenas genuinely reset), most allocators do not return freed
  pages to the OS, so **RSS reflects the high-water mark of allocator churn,
  not current live data** — and across ~1777 files, each contributing its
  own (size-dependent, sometimes large) transient peak, the OS-visible RSS
  can climb file-by-file even with zero true retention. This would explain
  why the *average* 160MB/file (measured over 403 files, this bug's original
  number) is larger than the ~36MB/file marginal measured over the first 17
  (smaller) files here — later files in the real `main.spl` closure include
  much larger compiler source files than these first ~20, and per-file churn
  scales with file size.

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

### Diagnostic instrumentation landed (safe, level-gated, kept)
`driver.spl` gained an env-gated (`SIMPLE_PARSE_RSS_PROBE=1`, default off)
per-file RSS probe in both `parse_all_impl` branches, printing to **stdout**
(`print`, not `eprint`/`log_phase`) since worker stderr is unreliable on some
native-build shapes. Shells out to `grep VmRSS /proc/self/status` rather than
using `rt_heap_registry_count()`/timing internals, because `text.to_i64()` was
found to be **broken on this native/cranelift path** — `"12345".trim().to_i64()`
returned `675995905`, not `12345`, when compiled and run via the stage3
binary (isolated repro: `rt_run_test/t.spl`). This looks like a real codegen
defect (a separate, tangential bug — not filed as its own doc yet; flagging
here since it was found in the course of this investigation and blocks
`to_i64()`-based instrumentation on this code path). The probe therefore
returns/prints the raw grep text rather than a parsed `i64`.

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
