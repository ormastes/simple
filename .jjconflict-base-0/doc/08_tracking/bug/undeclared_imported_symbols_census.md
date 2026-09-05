# Census: imported symbols that are declared nowhere in the repo

**Status:** OPEN — enumerated, triaged, not fixed (confirmed still accurate,
re-verified 2026-08-10)
**Filed:** 2026-08-05
**Scope:** owned `src/**` + `test/**` `.spl` (39,984 files). Vendored excluded:
`src/compiler_rust/vendor/**`, `src/runtime/vendor/**`,
`src/runtime/{miniaudio,stb_image,stb_truetype}.h`.
**Instrument:** static census, `scratchpad/undecl_census/census.py` (rerunnable
in principle — the script itself no longer exists on disk as of 2026-08-10,
since `scratchpad/` is per-session/ephemeral and was never committed; a fresh
full re-run of §9's four-step pipeline was not attempted this pass because
rebuilding the instrument is out of scope for a spot-check).
**Cross-checked against:** 4 real spec runs (see §5) and the compiler's own
`[use-warning]` oracle (see §6 — the oracle is **not deployed**, which is itself a
finding). **Spot-check 2026-08-10:** the first Appendix A.1 entry
(`src/app/dashboard/dashboard_collectors.spl:8` importing `DASHBOARD_TABLE_DIR`,
`load_table`, etc. from `app.dashboard.main`) was re-checked against
`src/app/dashboard/main.spl` — none of those names are declared there today,
confirming the census entry is still accurate and the underlying gap is still
unfixed. This is a spot-check of one cluster, not a full re-run; treat the
1,226-entry totals in §3 as last-measured 2026-08-05, not re-confirmed in full.

## 1. The family

A module writes `use some.module.{A, B}` where `A` is **declared nowhere in the
repo**. An unresolved *name* inside a module that does resolve is only a **warning**
(exit 0), so the module loads with the name simply absent and the code dies at
runtime. An unresolved *module* is a hard error, which kills the whole file before
any example runs — so a spec that is the only coverage for a feature reports
"1 failed" instead of "36 examples never ran".

Three instances surfaced by accident within hours of each other, each found only
because an unrelated lane tripped over it:

| # | symbols | outcome |
|---|---|---|
| 1 | `Matrix4`, `ComputedStyle`, `get_property_from_style` from `examples.browser.*` (a tree that never existed) | fixed in `e596c095fea` |
| 2 | `compute_object_fit`, `paint_scrollbar`; plus `PaintCommand.rect`, concealed behind the first error by the only-last-failure-per-example rule | fixed in `2d73d5d5768`, `ac59c74d7a0` |
| 3 | `interpolate_keyframes` from `std.gc_async_mut.gpu.browser_engine.style.animation` | still live, harmless today |

All three fixed names are absent from this census and instance 3 is present — the
census reproduces the known ground truth in both directions.

## 2. Prior art, and the half that was never swept

| doc | scope | covers this family? |
|---|---|---|
| `spec_imports_declared_nowhere_2026-08-04.md` | `test/**/*_spec.spl` only — 1,003 names / 294 specs | **spec-only** |
| `lib_specs_import_133_modules_that_do_not_exist_2026-08-04.md` | `test/01_unit/lib/`, `test/unit/lib/` — module paths, not names | spec-only |
| `code_quality_specs_import_modules_that_do_not_exist_2026-08-04.md` | 3 specs under `test/system/code_quality/` | spec-only |
| `src_os_dangling_imports_never_implemented_2026-07-28.md` | `src/os/**` + `src/unit/**` — 46 entries | src, **partial** |
| `use_list_names_never_checked_2026-08-04.md` | the compiler defect that makes this silent | mechanism |

**The gap is real and it is exactly where instances 1 and 2 lived:** no prior sweep
covered `src/**` outside `src/os`. Both fixed instances were in
`src/lib/gc_async_mut/gpu/browser_engine/`.

## 3. Result

**1,226 deduped entries, 766 distinct undeclared names, across 380 importing files.**
(2,244 raw entries before collapsing the duplicated `test/01_unit` ⇄ `test/unit`,
`test/03_system/feature` ⇄ `test/feature`, `test/08_web_platform` ⇄
`test/feature/web_platform` trees and the 683 generated `.spipe_matchers_*` mirrors.)

| bucket | `src/` | `test/` | total |
|---|---|---|---|
| **CONCEALED** — the importing file dies before any example runs | 57 (40 files) | 726 (186 specs) | **783** |
| **LIVE-AND-BROKEN** — the name is referenced; it dies at runtime | 68 (36 files) | 308 (107 specs) | **376** |
| **DEAD-AND-HARMLESS** — imported, never referenced | 25 (8 files) | 42 (29 specs) | **67** |

Full per-entry lists with `file:line`, the undeclared name, the importing module,
and the reference count are in **Appendix A** (`src/`, complete — all 150 entries)
and **Appendix B** (`test/`, grouped by spec).

## 4. Bucket definitions (and how each is decided)

- **CONCEALED** — the module path in the `use` resolves to no file anywhere. This is
  a hard `error: semantic: Cannot resolve module: …`, so the file produces **0
  executed examples** and reports as a single opaque failure. This is the worst
  bucket and the hardest to see: the loss is understated by the number of examples
  the spec would have run. Instance 2 was one of these. 144 distinct module paths
  are involved.
- **LIVE-AND-BROKEN** — the module resolves, the name does not, and the bound name
  is referenced in the importing file outside its `use` block. Warning only; the
  code runs and dies. These are real bugs.
- **DEAD-AND-HARMLESS** — module resolves, name does not, and nothing in the file
  ever references it. `interpolate_keyframes` is here today.

### Worst CONCEALED clusters

| unresolvable module | entries |
|---|---|
| `std.blink.layout.block_flow` | 36 |
| `std.blink.paint.paint_tree_walker` | 36 |
| `hardware.rv64gc.ext.rv64_float` | 31 |
| `hardware.rv64gc.ext.rv64_double` | 30 |
| `common.test_runner.display_detect` | 27 |
| `common.wine_proton_gate` | 22 |
| `std.blink.layout` | 18 |
| `compiler.backend.llvm_target` | 18 |
| `common.wine_proton_runtime` | 16 |
| `hardware.rv64gc.ext.rv64_atomics` | 15 |

### Worst CONCEALED specs (each reports one failure; each hides its whole example set)

`test/unit/lib/blink/form_paint_spec.spl` (17) ·
`test/unit/lib_standalone/blink/form_paint_spec.spl` (17) ·
`test/integration/hardware/rv32imac/rv32_core_smoke_spec.spl` (13) ·
`test/unit/hardware/rv64gc/rv64_fp_convert_d_spec.spl` (10) ·
`test/unit/hardware/rv64gc/rv64_fp_convert_s_spec.spl` (10) ·
`test/unit/lib/blink/paint_tree_walker_spec.spl` (10) ·
`test/unit/lib/common/rope_simd_search_test.spl` (10) ·
`test/unit/app/test/chrome_component_renderer_parity/diagnostics_spec.spl` (9) ·
`test/unit/app/ui/display_detect_spec.spl` (9) ·
`test/unit/lib/blink/image_paint_spec.spl` (9) ·
`test/unit/lib/blink/inline_flow_spec.spl` (9) ·
`test/03_system/rv64gc_spec.spl` (9)

The entire `std.blink.*` paint/layout family (`block_flow`, `paint_tree_walker`,
`layout`, `flex`, `dom.form_state`, `input.event`, `navigation.controller`) is the
single largest cluster. It is the same subsystem instances 1 and 2 came from.

## 5. Measured false-positive rate

**Sampled FP rate for "declared nowhere": 0 / 40 (0%).**

Method: 40 entries drawn at random (`random.seed(48)`; 20 from `src/`, 20 from
`test/`), each re-checked with an **independent** anchored `/usr/bin/grep -rE` over
all owned `.spl` for a definition-shaped line
(`^\s*(pub|export|extern|async|@extern)*\s*(fn|class|struct|enum|trait|mixin|actor|interface|type|alias|macro|val|var|let|const|global|object|me)\s+NAME\b`),
**plus** a string-literal search across `src/compiler_rust/**` and `src/runtime/**`
`.rs` to catch names the Rust seed registers as builtins with no `.spl`
declaration. All 40 came back with zero `.spl` definitions and zero Rust
registrations. Twelve were then re-checked with a bare unanchored whole-repo grep
across `.spl`/`.rs`/`.shs`: every one occurs only in the files that import or call
it, never in a definition.

**Non-defect rate: 1 / 40 (2.5%).** One sampled entry, `thing` in
`test/cert/tool_qual/negative/06_undefined_module_import.spl`, is an **intentional**
tool-qualification negative fixture. It is the only `test/cert/**/negative/` entry
in the whole census and is excluded from the buckets above.

**Bucket-assignment accuracy: 4 / 4** on the specs actually executed (§6).

`ugrep` is the default `grep` on this host; every counted pattern used
`/usr/bin/grep` explicitly and every symbol pattern was anchored. The
"declared-nowhere" predicate is self-limiting against generic-name noise — a
generic name is declared *somewhere* and is therefore filtered out automatically
— which is why no manual stop-list was needed.

## 6. Empirical validation

Four specs run individually with `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run <file>`,
output captured to a file (never `tail -1`):

| spec | predicted | observed | verdict |
|---|---|---|---|
| `test/unit/lib/blink/paint_tree_walker_spec.spl` | CONCEALED | `error: semantic: Cannot resolve module: std.blink.layout.block_flow`, EXIT=1, **0 examples executed** | ✔ |
| `test/unit/os/apps/terminal/terminal_spec.spl` | LIVE-AND-BROKEN | 40 examples executed, **36 failures**, EXIT=1 | ✔ |
| `test/feature/web_platform/css/animations_wpt_spec.spl` | DEAD-AND-HARMLESS | `5 examples, 0 failures`, EXIT=0 | ✔ |
| `test/feature/web_platform/css/wpt_scorecard_spec.spl` | DEAD-AND-HARMLESS | `26 examples, 0 failures`, EXIT=0 | ✔ |

The last two are instance 3 (`interpolate_keyframes`): the import is undeclared and
the suites are fully green — the definition of DEAD-AND-HARMLESS, and the reason it
was found only by luck.

### 6a. The `[use-warning]` oracle is not deployed — measured

The compiler emits
`[use-warning] '<name>' is named in \`use <mod>.{...}\` but module '<path>' does not
provide it (imported from <file>)`
from `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:508`. It
landed in `98e468602fd` (2026-08-04).

**The deployed binary does not contain it.**
`strings -a bin/release/x86_64-unknown-linux-gnu/simple | grep -c 'use-warning'`
returns **0** (binary dated 2026-08-04 02:04; the fix landed later that day). Every
one of the four runs above produced **zero** `[use-warning]` lines even where the
census and hand-verification both confirm an undeclared name — including
`interpolate_keyframes`, which the module genuinely does not provide and whose
surface is *not* opaque.

So the oracle exists in source but **fires nowhere on this host today**. That is why
this family surfaced three times by accident and never once by a run. Redeploying
the seed is the highest-value single action here; it was not done in this session
because a live rebuild of `bin/simple` races the parallel sessions using it.

### 6b. Oracle cross-check — built out-of-tree, then run

To use the oracle anyway, the seed was rebuilt into a scratch target
(`CARGO_TARGET_DIR=<scratch>/rt cargo build --release -p simple-driver`, `bin/simple`
left untouched). `strings -a <scratch>/rt/release/simple | grep -c use-warning`
returns 1 — the oracle is present. Four specs re-run with it emitted **34
`[use-warning]` lines, 16 distinct names**:

| oracle verdict | n | interpretation |
|---|---|---|
| in this census | 5 | `interpolate_keyframes`, `AnsiState`, `TerminalChar`, `TerminalLine`, `default_char` — exact agreement, all true family members |
| declared elsewhere in the repo, just not in the module imported from | 10 | `new_line` (declared in 8 files), `simd_add_u8x16`, `simd_aes_round`, `simd_aes_round_last`, `simd_clmul_hi_u64`, `simd_clmul_lo_u64`, `simd_xor_u64x2`, `simd_xor_u8x16`, `Vec16u8`, `Vec2u64` — a **different, also-silent defect** (wrong-module import), out of scope here |
| **oracle false positive** | 1 | `rt_font_glyph_advance` — declared as `extern fn` at `src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl:107`, *the very module it is imported from*. `collect_provided_names` does not count `extern fn` as provided, so the oracle warns on a name that is present. Census correctly excluded it. |

**Census names the oracle found that the census missed: 0.** Oracle precision for
this family on this sample: 5/16 (the other 11 are a different defect or a bug in the
oracle). This is why the static census, not the oracle, is the primary instrument
here — but the oracle is strictly better for the wrong-module axis, which the census
cannot see at all.

### 6b-bis. After deployment and the false-positive fix (2026-08-05)

The oracle is now **deployed** — `strings -a bin/release/x86_64-unknown-linux-gnu/simple
| grep -c use-warning` went `0` -> `1` — and the `extern fn` false positive is fixed.
Re-running the same four specs against the deployed binary:

| measure | census (pre-fix, scratch build) | now (deployed, post-fix) |
|---|---|---|
| `[use-warning]` lines | 34 | **25** |
| distinct names | 16 | **15** |
| census agreements retained | 5 | **5** — all of them |
| wrong-module names retained | 10 | **10** — all of them |
| oracle false positives | 1 | **0** |
| census names the oracle missed | 0 | **0** — unchanged |

The single distinct name that disappeared is `rt_font_glyph_advance`, the false
positive, and nothing else moved: agreement did not merely improve in aggregate, it
improved **only** on the axis the fix targeted. Precision for the declared-nowhere
family on this sample is now 5/15, and every remaining name is a real defect of one
of the two classes rather than an artifact of the checker.

Per-spec line counts now: `terminal_spec` 14, `animations_wpt_spec` 10,
`wpt_scorecard_spec` 1, `paint_tree_walker_spec` 0 (still zero — it is the CONCEALED
case, and blind spot 3 below explains why the oracle cannot see it by construction).

**A check now guards the deployment**, because the oracle vanishing from the build —
not any flaw in the oracle — is what made it useless for a day:
`scripts/check/check-use-warning-oracle-deployed.shs`. It runs the deployed binary
against a committed fixture and scores stderr content rather than exit status. A
source-presence check would not have caught the original defect: the source was
correct the entire time.

The oracle emitted **zero** warnings for `paint_tree_walker_spec.spl`, the CONCEALED
case — confirming blind spot 3 below.

Even once redeployed, the oracle has three structural blind spots that the static
census does not:

1. **Group imports only.** `warn_unprovided_use_names` returns early unless the
   `use` is a `{...}` group (`module_loader.rs:497`). Bare `use a.b.C` and
   `use a.b.*` are never checked.
2. **Opaque surfaces are skipped** — any module that re-exports via `export use x.*`
   or bare `export use {..}` is deliberately not checked (`module_loader.rs:433`),
   and this repo is full of them.
3. **Dynamic reach only.** A module is checked only if something loads it. Every
   `src/` module with no spec — most of Appendix A — is never reached at all. The
   CONCEALED bucket is invisible to it by construction: the module fails to resolve,
   so `provided` is never computed and no warning is possible.

4. ~~**`extern fn` is not counted as provided** (§6b) — the oracle false-positives on
   every `extern fn` re-export.~~ **FIXED 2026-08-05**, in the same change that
   deployed the oracle. `collect_provided_names` now folds in `Node::Extern` and
   `Node::ExternClass`. Only the extern *class* name is added, matching
   `Node::Class`, which likewise does not contribute its method names.

### 6c. The wrong-module class: kept separate, and deliberately NOT reclassified

10 of the 16 oracle hits were names that **are** declared in the repo, just not in
the module they are imported from. That is a different defect from "declared
nowhere", and the two must not be merged: the remedies have nothing in common. A
wrong-module import is a one-line fix with a known target — repoint the `use`. A
declared-nowhere import is an implementation decision about code that was never
written. Emitting them identically forces every reader to redo the "does this name
exist anywhere?" search by hand.

**Decision: the loader-time oracle keeps ONE diagnostic and must not try to split
them.** Reasons, in order of weight:

1. **It cannot prove the distinction.** Saying "declared nowhere" is a claim about
   the whole repo. The module loader sees one module and its siblings. The nearest
   existing machinery, `sibling_might_define_requested_names`
   (`module_loader.rs:262`), is a loose text probe scoped to *sibling files only*,
   so a name declared three directories away would be reported as "declared
   nowhere" — an overclaim, and precisely the kind of confident-but-wrong
   diagnostic that gets a checker switched off.
2. **The honest wording is already in place, and is worth protecting.** The current
   message says *"module 'm' does not provide it"* — not *"this name does not
   exist"*. That statement is exactly true for both classes and overclaims neither.
   It should stay that way.
3. **A repo-wide declaration index does not belong on the module-load path.**
   Splitting the classes correctly needs one, and building it per load is a
   filesystem sweep on the hot compile path.

So the split is real and stays visible — but it is the job of a **separate
repo-wide pass** (this census, and `spec_imports_declared_nowhere_2026-08-04.md`
for the spec axis), not of the loader. The oracle's role is to say "this import is
wrong"; naming *which* of the two ways it is wrong is a second instrument's job.
The two classes are counted separately in §6a above and are not to be summed.

Conversely the census cannot see what the oracle can: (a) names the Rust seed injects
at runtime with no `.spl` declaration — the Rust string-literal cross-check in §5
found none in 40 samples, but it is a heuristic, not a proof; and (b) the
**wrong-module** axis, where the imported name exists somewhere but not in the module
named — 10 of the 16 oracle hits were this, so it is not a rare case.

## 7. What this method cannot see

- **Only braced `use a.b.{X, Y}` imports are censused.** Bare `use a.b.C` and glob
  `use a.b.*` are out of scope — the same defect through those forms is invisible
  here. This matches the compiler's own checker, so neither instrument covers them.
- **A name declared *somewhere else* than the module it is imported from is not
  reported.** The predicate is "declared nowhere in the repo", which is the family
  as defined. A wrong-module import of a name that does exist elsewhere is a
  different (and also silent) defect; `spec_imports_declared_nowhere_2026-08-04.md`
  covers that axis for specs only.
- **Rust-seed builtins** with no `.spl` declaration would read as undeclared. The §5
  cross-check found none, but the search is by string literal and can miss a
  macro-generated registration.
- **The declaration index is textual.** Names produced only at runtime — dynamic
  registration, generated code, `impl` blocks with a form the regex misses — could
  read as undeclared. Zero such cases appeared in the 40-sample hand check.
- **`bin/simple test <dir>` produced no verdict lines at all** for
  `test/feature/web_platform` (exit 0, 3,179 lines of pure lint noise, zero
  `Results:` and zero `SPEC FILE VERDICT:`). Directory-scope test runs could not be
  used as an instrument; every measurement here is per-file `bin/simple run`.

## 8. What was fixed, and what was left

**Nothing was fixed in this pass. This is deliberate.**

- The 783 CONCEALED and 376 LIVE-AND-BROKEN entries are not import typos — they are
  imports of code that was **never written** (144 distinct module paths that exist
  nowhere). Each needs an implementation or a deletion decision, not an edit. That
  is per-cluster work, not a sweep.
- The 67 DEAD-AND-HARMLESS entries could be deleted mechanically, but a dead import
  is the only surviving marker that an API was planned and never built. Deleting
  them silently converts a visible gap into no record at all, and it is a bulk edit
  across 37 files. Left for a per-cluster decision.
- ~~**The one action that is unambiguously worth taking is redeploying the seed** so
  `[use-warning]` fires (§6a). Not done here to avoid racing parallel sessions on
  `bin/simple`. Fix the `extern fn` false positive (§6b) in the same change, or the
  warning will be noisy from day one and get ignored.~~ **DONE 2026-08-05** — seed
  rebuilt and redeployed, `extern fn` false positive fixed in the same change, and
  `scripts/check/check-use-warning-oracle-deployed.shs` added so the deployment
  cannot silently regress again. Results in §6b-bis. Still nothing fixed in the
  1,159 undeclared imports themselves; that remains deliberate.

Recommended order of attack, by blast radius:

1. `std.blink.*` paint/layout family — 36+36+18+14+14+14+12 entries, ~14 CONCEALED
   specs, same subsystem as instances 1 and 2.
2. `hardware.rv64gc.ext.rv64_{float,double,atomics}` — 76 entries, 4+ CONCEALED
   specs covering RV64 FP compliance.
3. `common.wine_proton_*` (38) and `common.test_runner.display_detect` (27).
4. `src/` LIVE-AND-BROKEN, 68 entries — no spec covers them, so nothing will ever
   report them; see Appendix A.1.

## 9. Reproduction

```sh
python3 scratchpad/undecl_census/census.py census.json   # census
python3 scratchpad/undecl_census/triage.py               # dedupe + module resolution
python3 scratchpad/undecl_census/buckets.py              # bucket assignment
python3 scratchpad/undecl_census/sample.py               # 40-entry hand-verification
```

## Appendix A — `src/` entries (all 150, complete)

### A.1 LIVE-AND-BROKEN — 68 entries in 36 files

| importing module (file:line) | undeclared name | imported from | refs in file |
|---|---|---|---|
| `src/app/cli/_CliMain/main_and_help.spl:33` | `t32_cli_main` | `app.t32_cli.mod` | 2 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `DASHBOARD_TABLE_DIR` | `app.dashboard.main` | 10 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `count_nonempty` | `app.dashboard.main` | 1 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `itos` | `app.dashboard.main` | 25 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `load_table` | `app.dashboard.main` | 4 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `load_table_named` | `app.dashboard.main` | 6 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `sum_int` | `app.dashboard.main` | 6 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `today_date` | `app.dashboard.main` | 4 |
| `src/app/dashboard/dashboard_collectors.spl:8` | `write_table` | `app.dashboard.main` | 6 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `DASHBOARD_CACHE_PATH` | `app.dashboard.main` | 2 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `DASHBOARD_HISTORY_DIR` | `app.dashboard.main` | 1 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `DASHBOARD_TABLE_DIR` | `app.dashboard.main` | 3 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `TABLE_COUNT` | `app.dashboard.main` | 3 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `TABLE_HEADERS` | `app.dashboard.main` | 1 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `TABLE_NAMES` | `app.dashboard.main` | 2 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `current_month` | `app.dashboard.main` | 1 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `load_table` | `app.dashboard.main` | 2 |
| `src/app/dashboard/dashboard_export_runtime.spl:7` | `today_date` | `app.dashboard.main` | 1 |
| `src/app/hosted_apps/file_manager_client.spl:1` | `file_manager_remote_main` | `os.apps.file_manager.file_manager` | 1 |
| `src/app/hosted_apps/hello_world_client.spl:1` | `hello_world_remote_main` | `os.apps.hello_world.hello_world` | 1 |
| `src/app/hosted_apps/simple_browser_client.spl:1` | `simple_browser_remote_main` | `os.apps.simple_browser.simple_browser` | 1 |
| ~~`src/app/office/sheets/math_bridge.spl:17`~~ | ~~`variance_sample`~~ | `std.common.math.statistics` | 1 | FIXED 2026-08-17 (see note below) |

> **`variance_sample` — FIXED 2026-08-17, SOURCE-VERIFIED ONLY, NOT EXECUTION-VERIFIED.**
> `math_bridge.spl:18` imported and `:156` called `variance_sample`; `src/lib/common/math/statistics.spl`
> has zero definitions of that name and no other module provides it (`/usr/bin/grep -rn variance_sample`
> over the tree hits only these two source lines plus docs/plans). The stdlib counterpart is
> `var_sample` (statistics.spl:121), whose body divides by `(n - 1)` — genuine SAMPLE variance,
> matching `excel_var`'s "SAMPLE VARIANCE (n-1 denominator)" contract; `var_pop` (:110) divides by
> `n` and is NOT the right target. Fix direction: renamed the USE, not the library, because
> statistics.spl's family is `var_pop`/`var_sample`/`stdev_pop`/`stdev_sample` — adding a
> `variance_sample` alias would break that convention and add a duplicate public API for one caller.
> **A compiler deploy was in progress, so nothing was executed. This fix is reasoned from source
> only.** Deferred verification command:
> `bin/simple test test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl`
> (per `.claude/rules/testing.md`: exit 0 is NOT a pass — require an explicit results/count line).
> Regression spec added by the same commit and likewise UNVERIFIED.
| `src/app/simple_process_manager/wm_spm_client.spl:21` | `window_record_encode` | `lib.common.win_fs.window_record` | 1 |
| `src/app/test/x25519mlkem768_coverage_contract.spl:3` | `CoverageOwnerOutcomeSummary` | `std.test_runner.test_runner_coverage` | 1 |
| `src/app/test/x25519mlkem768_coverage_receipt.spl:15` | `CoverageOwnerOutcomeSummary` | `std.test_runner.test_runner_coverage` | 1 |
| `src/app/test/x25519mlkem768_coverage_receipt.spl:15` | `check_critical_branch_outcomes` | `std.test_runner.test_runner_coverage` | 1 |
| `src/app/test/x25519mlkem768_coverage_receipt.spl:15` | `coverage_owner_outcome_summary` | `std.test_runner.test_runner_coverage` | 1 |
| `src/app/test/x25519mlkem768_critical_inventory.spl:9` | `file_create_exclusive` | `app.io.mod` | 1 |
| `src/app/test/x25519mlkem768_gpu_binding.spl:5` | `file_create_exclusive` | `app.io.mod` | 1 |
| `src/compiler_rust/lib/std/src/type_checker/type_inference.spl:5` | `Vec` | `std.collections` | 16 |
| `src/lib/gc_async_mut/compress/__init__.spl:24` | `CompressionFormat` | `std.compress` | 7 |
| `src/lib/gc_async_mut/compress/__init__.spl:99` | `GzipCompressor` | `std.compress` | 1 |
| `src/lib/gc_async_mut/engine/render/shader.spl:17` | `shader_compiler_get_or_compile_spirv` | `std.nogc_sync_mut.engine.render.shader_compile` | 1 |
| `src/lib/gc_async_mut/js/engine/interpreter_native.spl:16` | `_resolve_fetch_url` | `std.gc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/gc_async_mut/js/engine/interpreter_native.spl:16` | `_simple_fetch_base_url` | `std.gc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/gc_async_mut/js/engine/interpreter_native.spl:16` | `_simple_fetch_cookie_header` | `std.gc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/gc_async_mut/js/engine/interpreter_native.spl:16` | `_simple_fetch_marker` | `std.gc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/nogc_async_mut/async_host/__init__.spl:42` | `SocketHandle` | `std.async_host.handle` | 1 |
| `src/lib/nogc_async_mut/async_host/__init__.spl:31` | `spawn_blocking` | `std.async_host.future` | 1 |
| `src/lib/nogc_async_mut/compress/__init__.spl:24` | `CompressionFormat` | `std.compress` | 7 |
| `src/lib/nogc_async_mut/compress/__init__.spl:99` | `GzipCompressor` | `std.compress` | 1 |
| `src/lib/nogc_async_mut/fs_driver/fat32_core.spl:11` | `_parse_lfn_slot` | `std.fs_driver.fat32_parsers` | 1 |
| `src/lib/nogc_async_mut/js/engine/interpreter_native.spl:12` | `_resolve_fetch_url` | `std.nogc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/nogc_async_mut/js/engine/interpreter_native.spl:12` | `_simple_fetch_base_url` | `std.nogc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/nogc_async_mut/js/engine/interpreter_native.spl:12` | `_simple_fetch_cookie_header` | `std.nogc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/nogc_async_mut/js/engine/interpreter_native.spl:12` | `_simple_fetch_marker` | `std.nogc_async_mut.js.engine.interpreter` | 1 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:24` | `CompressionFormat` | `std.compress` | 7 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:99` | `GzipCompressor` | `std.compress` | 1 |
| `src/os/compositor/animation_controller.spl:7` | `spring_progress` | `common.animation.spring` | 1 |
| `src/os/compositor/engine2d_render_evidence.spl:17` | `FirmwareSha256` | `os.drivers.framebuffer.ramfb` | 1 |
| `src/os/compositor/engine2d_render_evidence.spl:17` | `parse_sha256_hex_words` | `os.drivers.framebuffer.ramfb` | 1 |
| `src/os/compositor/fb_backend.spl:20` | `FbCompositorBackend` | `os.compositor.display_backend` | 1 |
| `src/os/compositor/window_effects.spl:13` | `draw_text_shadow` | `os.compositor.text_render` | 1 |
| `src/os/crypto/ecdsa_p521.spl:35` | `mod_exp` | `std.math.bignum.bignat` | 2 |
| `src/os/desktop/shell.spl:50` | `WM_STATUS_ERROR` | `common.window_protocol.window_protocol` | 1 |
| `src/os/desktop/shell_types.spl:11` | `noalloc_log_debug` | `std.nogc_async_mut_noalloc.log` | 4 |
| `src/os/desktop/shell_ui_builders.spl:23` | `FileExplorer` | `os.apps.file_explorer.file_explorer` | 1 |
| `src/os/kernel/boot/boot_fs.spl:11` | `current_architecture` | `os.kernel.arch.arch_context` | 2 |
| `src/os/kernel/fs/win_vfs/win_vfs_driver.spl:19` | `tree_read` | `lib.common.win_fs.fs_encoder` | 1 |
| `src/os/kernel/fs/win_vfs/win_vfs_driver.spl:19` | `tree_readdir` | `lib.common.win_fs.fs_encoder` | 1 |
| `src/os/services/audio/audio_service.spl:13` | `hda_dma_write_pcm_i16` | `os.drivers.audio.hda_dma_resources` | 1 |
| `src/os/services/init/init_service.spl:8` | `spawn_binary_with_args` | `os.userlib.process` | 1 |
| `src/os/services/wm/wm_codec.spl:8` | `WM_STATUS_OK` | `common.window_protocol.window_protocol` | 1 |
| `src/os/services/wm/wm_codec.spl:8` | `WmStatus` | `common.window_protocol.window_protocol` | 1 |
| `src/os/services/wm/wm_service.spl:32` | `WM_STATUS_NO_SPACE` | `common.window_protocol.window_protocol` | 2 |
| `src/os/userlib/_Window/client_methods.spl:32` | `WM_EVENT_FOCUS` | `common.window_protocol.window_protocol` | 1 |
| `src/os/userlib/_Window/client_methods.spl:32` | `WM_STATUS_OK` | `common.window_protocol.window_protocol` | 1 |
| `src/os/userlib/_Window/client_methods.spl:32` | `wm_input_event` | `common.window_protocol.window_protocol` | 5 |

### A.2 CONCEALED — 57 entries in 40 files

| importing module (file:line) | undeclared name | imported from | refs in file |
|---|---|---|---|
| `src/app/cli/query_check.spl:16` | `LspEmitter` | `std.report.emitter.lsp` | 3 |
| `src/app/cli/query_commands.spl:22` | `LspEmitter` | `std.report.emitter.lsp` | 1 |
| `src/app/cli/query_navigation.spl:12` | `LspEmitter` | `std.report.emitter.lsp` | 1 |
| `src/app/composite_test_entry.spl:10` | `BaremetalBuilder` | `app.build.baremetal` | 1 |
| `src/app/composite_test_entry.spl:10` | `baremetal_config_riscv` | `app.build.baremetal` | 1 |
| `src/app/composite_test_entry.spl:10` | `baremetal_config_riscv32` | `app.build.baremetal` | 1 |
| `src/app/dev/shb_emit.spl:13` | `parse_extract_write_shb` | `compiler.shb.shb_extractor` | 1 |
| `src/app/lint/render_adapter.spl:12` | `QualityResult` | `app.build.quality` | 2 |
| `src/app/test/x25519mlkem768_candidate_batch_measurement.spl:38` | `platform_measurement_refresh_process_rss` | `std.nogc_sync_mut.platform_measurement_observer` | 1 |
| `src/app/test_runner_new/test_db_migrate.spl:6` | `test_database_load` | `app.test_runner_new.test_db_core` | 2 |
| `src/app/test_runner_new/test_db_perf.spl:5` | `test_database_load` | `app.test_runner_new.test_db_core` | 1 |
| `src/app/ui.render/core.spl:18` | `default_check_config` | `app.build.quality` | 1 |
| `src/app/ui.render/core.spl:18` | `default_lint_config` | `app.build.quality` | 1 |
| `src/app/ui.render/core.spl:21` | `orchestrate_build` | `app.build.orchestrator` | 1 |
| `src/app/ui.render/core.spl:20` | `parse_build_args` | `app.build.config` | 1 |
| `src/app/ui.render/core.spl:16` | `render_build` | `app.build.render_adapter` | 1 |
| `src/compiler/10.frontend/core/compiler/test_mir_codegen.spl:10` | `mir_codegen_program` | `compiler.core.compiler.mir_codegen` | 1 |
| `src/compiler/35.semantics/lint/duplicate_typed_args.spl:25` | `decl_get_params` | `compiler.core.ast` | 1 |
| `src/compiler/90.tools/leak_check/static_runner.spl:10` | `check_alloc_imports` | `compiler.driver.build` | 1 |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl:16` | `FullscreenMode` | `ui.gui.vulkan_window` | 2 |
| `src/compiler_rust/lib/std/examples/vulkan_gui_demo.spl:16` | `WindowEvent` | `ui.gui.vulkan_window` | 5 |
| `src/compiler_rust/lib/std/src/net/tcp.spl:7` | `error_from_code` | `net` | 11 |
| `src/compiler_rust/lib/std/src/net/udp.spl:7` | `error_from_code` | `net` | 11 |
| `src/compiler_rust/lib/std/src/tooling/core/project_detector.spl:5` | `DirPath` | `host.common.io.types` | 2 |
| `src/compiler_rust/lib/std/src/tooling/core/project_ops.spl:5` | `DirPath` | `host.common.io.types` | 1 |
| `src/compiler_rust/lib/std/src/tooling/dashboard/snapshots.spl:7` | `date_diff_days` | `core.time` | 2 |
| `src/compiler_rust/lib/std/src/tooling/deployment/automation_tasks.spl:7` | `HttpUrl` | `host.common.net.types` | 1 |
| `src/compiler_rust/lib/std/src/tooling/deployment/pipeline.spl:8` | `HttpUrl` | `host.common.net.types` | 2 |
| `src/compiler_rust/lib/std/src/tooling/testing/discovery.spl:9` | `DirPath` | `host.common.io.types` | 3 |
| `src/compiler_rust/lib/std/src/verification/lean/runner.spl:10` | `monotonic_ms` | `host.process` | 3 |
| `src/lib/gc_async_mut/gpu/browser_engine/layout_core.spl:22` | `text_char_width` | `common.text_layout.text_layout` | 1 |
| `src/lib/gc_async_mut/gpu/browser_engine/layout_core.spl:22` | `text_line_height` | `common.text_layout.text_layout` | 1 |
| `src/lib/nogc_async_mut/actors/__init__.spl:108` | `RestartStrategy` | `std.actors.supervisor` | 1 |
| `src/lib/nogc_async_mut/mcp/editor.spl:6` | `fs_read_text` | `host.async_nogc_mut.io.fs` | 1 |
| `src/lib/nogc_async_mut/mcp/editor.spl:6` | `fs_write_text` | `host.async_nogc_mut.io.fs` | 1 |
| `src/lib/nogc_sync_mut/baremetal/host_comm.spl:8` | `create_loopback` | `std.nogc_sync_mut.baremetal.factory` | 2 |
| `src/lib/nogc_sync_mut/baremetal/mod.spl:12` | `create_loopback` | `std.nogc_sync_mut.baremetal.factory` | 0 |
| `src/lib/nogc_sync_mut/fuzz.spl:16` | `random_choice` | `std.random_utils` | 3 |
| `src/lib/nogc_sync_mut/fuzz.spl:16` | `rng_create` | `std.random_utils` | 2 |
| `src/lib/nogc_sync_mut/fuzz.spl:16` | `rng_next_range` | `std.random_utils` | 26 |
| `src/lib/nogc_sync_mut/gpu/engine2d/webgpu_surface.spl:3` | `webgpu_sffi_readback_checksum` | `std.common.gpu.webgpu_sffi` | 1 |
| `src/os/apps/browser_sample/browser_sample.spl:30` | `execute_scene_to_buffer` | `common.render_scene.executor` | 2 |
| `src/os/compositor/browser_backend.spl:26` | `execute_scene_to_buffer` | `common.render_scene.executor` | 2 |
| `src/os/crypto/ecdh_p256.spl:46` | `FeP256` | `std.common.math.field.fe_p256` | 17 |
| `src/os/crypto/p256.spl:21` | `FeP256` | `std.common.math.field.fe_p256` | 2 |
| `src/os/crypto/pem.spl:22` | `line_unwrap` | `base_encoding.utilities` | 2 |
| `src/os/crypto/pem.spl:22` | `line_wrap` | `base_encoding.utilities` | 2 |
| `src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl:7` | `CryptoCudaSession` | `std.gc_async_mut.crypto_accel.cuda_session` | 3 |
| `src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl:5` | `CryptoMetalSession` | `std.gc_async_mut.crypto_accel.metal_session` | 4 |
| `src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl:5` | `CryptoVulkanSession` | `std.gc_async_mut.crypto_accel.vulkan_session` | 2 |
| `src/os/hosted/hosted_entry.spl:80` | `hosted_browser_animation_evidence` | `os.hosted.hosted_browser_render_evidence` | 1 |
| `src/os/hosted/hosted_entry.spl:80` | `hosted_browser_html_css_evidence` | `os.hosted.hosted_browser_render_evidence` | 1 |
| `src/os/services/display/display_service.spl:15` | `DisplayMode` | `common.display_protocol.display_protocol` | 3 |
| `src/os/services/display/display_service.spl:15` | `PIXEL_FORMAT_BGRA8` | `common.display_protocol.display_protocol` | 2 |
| `src/os/services/display/display_service.spl:15` | `SurfaceDesc` | `common.display_protocol.display_protocol` | 5 |
| `src/os/services/display/display_service.spl:15` | `display_mode` | `common.display_protocol.display_protocol` | 2 |
| `src/os/services/display/display_service.spl:15` | `surface_desc` | `common.display_protocol.display_protocol` | 2 |

### A.3 DEAD-AND-HARMLESS — 25 entries in 8 files

| importing module (file:line) | undeclared name | imported from | refs in file |
|---|---|---|---|
| `src/lib/common/hpack/decoder.spl:17` | `_append_bytes` | `std.common.hpack.encoder` | 0 |
| `src/lib/gc_async_mut/compress/__init__.spl:99` | `GzipDecompressor` | `std.compress` | 0 |
| `src/lib/gc_async_mut/compress/__init__.spl:31` | `bzip2_compress` | `std.compress` | 0 |
| `src/lib/gc_async_mut/compress/__init__.spl:31` | `bzip2_decompress` | `std.compress` | 0 |
| `src/lib/gc_async_mut/compress/__init__.spl:30` | `zlib_compress` | `std.compress` | 0 |
| `src/lib/gc_async_mut/compress/__init__.spl:30` | `zlib_decompress` | `std.compress` | 0 |
| `src/lib/gc_async_mut/compress/__init__.spl:33` | `zstd_compress` | `std.compress` | 0 |
| `src/lib/gc_async_mut/gpu/engine2d/helpers_clip.spl:7` | `clip_rect_intersect` | `std.gpu.engine2d.helpers_clip` | 0 |
| `src/lib/nogc_async_mut/compress/__init__.spl:99` | `GzipDecompressor` | `std.compress` | 0 |
| `src/lib/nogc_async_mut/compress/__init__.spl:31` | `bzip2_compress` | `std.compress` | 0 |
| `src/lib/nogc_async_mut/compress/__init__.spl:31` | `bzip2_decompress` | `std.compress` | 0 |
| `src/lib/nogc_async_mut/compress/__init__.spl:30` | `zlib_compress` | `std.compress` | 0 |
| `src/lib/nogc_async_mut/compress/__init__.spl:30` | `zlib_decompress` | `std.compress` | 0 |
| `src/lib/nogc_async_mut/compress/__init__.spl:33` | `zstd_compress` | `std.compress` | 0 |
| `src/lib/nogc_async_mut/engine/render/shader_compile.spl:7` | `shader_compiler_get_or_compile_spirv` | `std.nogc_sync_mut.engine.render.shader_compile` | 0 |
| `src/lib/nogc_async_mut/engine/render/shader_compile.spl:7` | `shader_compiler_get_or_compile_wgsl` | `std.nogc_sync_mut.engine.render.shader_compile` | 0 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:99` | `GzipDecompressor` | `std.compress` | 0 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:31` | `bzip2_compress` | `std.compress` | 0 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:31` | `bzip2_decompress` | `std.compress` | 0 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:30` | `zlib_compress` | `std.compress` | 0 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:30` | `zlib_decompress` | `std.compress` | 0 |
| `src/lib/nogc_sync_mut/compress/__init__.spl:33` | `zstd_compress` | `std.compress` | 0 |
| `src/lib/nogc_sync_mut/gpu/__init__.spl:18` | `get_default_gpu` | `std.nogc_sync_mut.gpu.device` | 0 |
| `src/lib/nogc_sync_mut/gpu/__init__.spl:18` | `list_gpus` | `std.nogc_sync_mut.gpu.device` | 0 |
| `src/os/compositor/mod.spl:30` | `draw_text_shadow` | `os.compositor.text_render` | 0 |

## Appendix B — `test/` entries, grouped by importing spec (deduped)

### B.1 CONCEALED — 726 entries across 186 specs

| spec (canonical) | n | undeclared names | modules |
|---|---|---|---|
| `test/unit/lib/blink/form_paint_spec.spl` (L19) | 17 | `BoxGeometry`, `FormFieldEntry`, `FormFieldPaintEntry`, `FormState`, `ImageEntry`, `PaintContext`, `StyledBox`, `box_geometry_new`, `collect_display_list`, `finalize_paint`, `form_state_empty`, `form_state_get_placeholder`, `form_state_get_value`, `form_state_set_value`, `form_state_with_field`, `layout_box_new`, `paint_tree_new_with_forms` | `std.blink.dom.form_state`, `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| `test/unit/lib_standalone/blink/form_paint_spec.spl` (L19) | 17 | `BoxGeometry`, `FormFieldEntry`, `FormFieldPaintEntry`, `FormState`, `ImageEntry`, `PaintContext`, `StyledBox`, `box_geometry_new`, `collect_display_list`, `finalize_paint`, `form_state_empty`, `form_state_get_placeholder`, `form_state_get_value`, `form_state_set_value`, `form_state_with_field`, `layout_box_new`, `paint_tree_new_with_forms` | `std.blink.dom.form_state`, `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| `test/integration/hardware/rv32imac/rv32_core_smoke_spec.spl` (L23) | 13 | `AluOp`, `BranchOp`, `decode_funct3`, `decode_funct7`, `decode_imm_b`, `decode_imm_i`, `decode_imm_j`, `decode_imm_s`, `decode_imm_u`, `decode_opcode`, `decode_rd`, `decode_rs1`, `decode_rs2` | `hardware.riscv_common.core.riscv_decode`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| `test/unit/hardware/rv64gc/rv64_fp_convert_d_spec.spl` (L18) | 10 | `fcvt_d_l`, `fcvt_d_s`, `fcvt_d_w`, `fcvt_d_wu`, `fcvt_l_d`, `fcvt_s_d`, `fcvt_w_d`, `fcvt_wu_d`, `fmv_d_x`, `fmv_x_d` | `hardware.rv64gc.ext.rv64_double` |
| `test/unit/hardware/rv64gc/rv64_fp_convert_s_spec.spl` (L18) | 10 | `fcvt_l_s`, `fcvt_lu_s`, `fcvt_s_l`, `fcvt_s_lu`, `fcvt_s_w`, `fcvt_s_wu`, `fcvt_w_s`, `fcvt_wu_s`, `fmv_w_x`, `fmv_x_w` | `hardware.rv64gc.ext.rv64_float` |
| `test/unit/lib/blink/paint_tree_walker_spec.spl` (L16) | 10 | `BoxGeometry`, `PaintContext`, `StyledBox`, `box_geometry_new`, `box_geometry_zero`, `computed_style_default`, `finalize_paint`, `layout_box_new`, `paint_tree`, `paint_tree_new` | `std.blink.entity.computed_style`, `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| `test/unit/lib/common/rope_simd_search_test.spl` (L4) | 10 | `rope_contains`, `rope_ends_with`, `rope_equals`, `rope_find`, `rope_find_all`, `rope_length`, `rope_starts_with`, `rope_to_lower`, `rope_to_string`, `rope_to_upper` | `common.rope.search`, `common.rope.types`, `common.rope.utilities` |
| `test/unit/lib_standalone/blink/paint_tree_walker_spec.spl` (L16) | 10 | `BoxGeometry`, `PaintContext`, `StyledBox`, `box_geometry_new`, `box_geometry_zero`, `computed_style_default`, `finalize_paint`, `layout_box_new`, `paint_tree`, `paint_tree_new` | `std.blink.entity.computed_style`, `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| `test/unit/app/test/chrome_component_renderer_parity/diagnostics_spec.spl` (L4) | 9 | `CanonicalRenderOutput`, `ParityDiagnosticPlan`, `backend_evidence_v1`, `canonical_render_output_v1`, `compare_rgba8_with_policy`, `rendering_stage_record_v1`, `stable_bytes_checksum`, `validate_parity_mismatch_artifacts`, `write_parity_mismatch_artifacts` | `app.test.chrome_component_renderer_parity.diagnostics`, `common.ui.rendering_parity`, `common.ui.rendering_parity.checksum` |
| `test/unit/app/ui/display_detect_spec.spl` (L5) | 9 | `DISPLAY_MACOS`, `DISPLAY_NONE`, `DISPLAY_WAYLAND`, `DISPLAY_X11`, `DISPLAY_XVFB`, `can_show_gui`, `detect_display`, `display_kind_name`, `has_any_display` | `common.test_runner.display_detect` |
| `test/unit/lib/blink/image_paint_spec.spl` (L18) | 9 | `BoxGeometry`, `ImageEntry`, `PaintContext`, `StyledBox`, `box_geometry_new`, `collect_display_list`, `finalize_paint`, `layout_box_new`, `paint_tree_new_with_images` | `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| `test/unit/lib/blink/inline_flow_spec.spl` (L18) | 9 | `InlineBox`, `InlineItem`, `InlineItemKind`, `InlineLayoutResult`, `estimate_text_width`, `inline_element`, `inline_text`, `layout_inline_flow`, `wrap_text_run` | `std.blink.layout` |
| `test/unit/lib_standalone/blink/image_paint_spec.spl` (L18) | 9 | `BoxGeometry`, `ImageEntry`, `PaintContext`, `StyledBox`, `box_geometry_new`, `collect_display_list`, `finalize_paint`, `layout_box_new`, `paint_tree_new_with_images` | `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| `test/unit/lib_standalone/blink/inline_flow_spec.spl` (L18) | 9 | `InlineBox`, `InlineItem`, `InlineItemKind`, `InlineLayoutResult`, `estimate_text_width`, `inline_element`, `inline_text`, `layout_inline_flow`, `wrap_text_run` | `std.blink.layout` |
| `test/03_system/rv64gc_spec.spl` (L7) | 9 | `AluOp`, `AmoOp`, `F3_ADD_SUB`, `F7_NORMAL`, `F7_SUB_SRA`, `MulDivOp`, `alu_execute`, `amo_execute`, `decode_alu_op` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, `hardware.rv64gc.pkg.rv64_isa_pkg`, `hardware.rv64gc.pkg.rv64_types_pkg` |
| `test/03_system/gui/container_detect_spec.spl` (L30) | 9 | `DISPLAY_MACOS`, `DISPLAY_NONE`, `DISPLAY_WAYLAND`, `DISPLAY_X11`, `DISPLAY_XVFB`, `can_show_gui`, `detect_display`, `display_kind_name`, `has_any_display` | `common.test_runner.display_detect` |
| `test/03_system/hardware/rv64gc_spec.spl` (L7) | 9 | `AluOp`, `AmoOp`, `F3_ADD_SUB`, `F7_NORMAL`, `F7_SUB_SRA`, `MulDivOp`, `alu_execute`, `amo_execute`, `decode_alu_op` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, `hardware.rv64gc.pkg.rv64_isa_pkg`, `hardware.rv64gc.pkg.rv64_types_pkg` |
| `test/system/coverage/coverage_build_spec.spl` (L49) | 9 | `CoverageConfig`, `CoverageFormat`, `CoverageLevel`, `build_coverage_args`, `default_coverage_config`, `format_to_string`, `parse_coverage_lines`, `parse_coverage_percent`, `power_of_10` | `compiler.driver.build.coverage` |
| `test/system/gui/container_detect_spec.spl` (L30) | 9 | `DISPLAY_MACOS`, `DISPLAY_NONE`, `DISPLAY_WAYLAND`, `DISPLAY_X11`, `DISPLAY_XVFB`, `can_show_gui`, `detect_display`, `display_kind_name`, `has_any_display` | `common.test_runner.display_detect` |
| `test/system/rv64gc_spec.spl` (L7) | 9 | `AluOp`, `AmoOp`, `F3_ADD_SUB`, `F7_NORMAL`, `F7_SUB_SRA`, `MulDivOp`, `alu_execute`, `amo_execute`, `decode_alu_op` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, `hardware.rv64gc.pkg.rv64_isa_pkg`, `hardware.rv64gc.pkg.rv64_types_pkg` |
| `test/unit/lib/blink/hit_test_spec.spl` (L17) | 8 | `BoxGeometry`, `box_geometry_new`, `box_geometry_zero`, `hit_test_ancestors`, `hit_test_empty`, `hit_test_event`, `layout_box_new`, `mouse_event` | `std.blink.input.event`, `std.blink.input.hit_test`, `std.blink.layout.block_flow` |
| `test/unit/lib_standalone/blink/hit_test_spec.spl` (L17) | 8 | `BoxGeometry`, `box_geometry_new`, `box_geometry_zero`, `hit_test_ancestors`, `hit_test_empty`, `hit_test_event`, `layout_box_new`, `mouse_event` | `std.blink.input.event`, `std.blink.input.hit_test`, `std.blink.layout.block_flow` |
| `test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl` (L18) | 8 | `fcvt_d_s`, `fcvt_s_d`, `fp_add_d`, `fp_add_s`, `fp_div_d`, `fp_div_s`, `fp_mul_d`, `fp_mul_s` | `hardware.rv64gc.ext.rv64_double`, `hardware.rv64gc.ext.rv64_float` |
| `test/unit/compiler/build/ffi_plumbing_spec.spl` (L9) | 7 | `build_ffi_generator_args`, `ffi_generation_skip_env_name`, `ffi_generator_output_dir`, `ffi_generator_script_path`, `ffi_workspace_manifest_path`, `ffi_workspace_root`, `ffi_workspace_source_path` | `app.build.orchestrator` |
| `test/unit/lib/blink/flex_spec.spl` (L16) | 7 | `AlignItems`, `FlexContainer`, `FlexDirection`, `JustifyContent`, `flex_container_column`, `flex_container_row`, `flex_item_new` | `std.blink.layout.flex` |
| `test/unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl` (L5) | 7 | `ENGINE2D_PARITY_CONVERTER`, `engine2d_rendering_parity_backend_name`, `engine2d_rendering_parity_canonicalize`, `engine2d_rendering_parity_evidence`, `engine2d_rendering_parity_execute_composition`, `simple_web_rendering_parity_observe`, `simple_web_rendering_parity_stage_records_from_observation` | `std.gc_async_mut.gpu.browser_engine.rendering_parity_adapter`, `std.gc_async_mut.gpu.engine2d.rendering_parity_adapter` |
| `test/unit/lib_standalone/blink/flex_spec.spl` (L16) | 7 | `AlignItems`, `FlexContainer`, `FlexDirection`, `JustifyContent`, `flex_container_column`, `flex_container_row`, `flex_item_new` | `std.blink.layout.flex` |
| `test/03_system/app/simpleos/feature/simpleos_proton_substrate_spec.spl` (L1) | 7 | `wine_proton_feature_gate`, `wine_proton_fixture_features`, `wine_proton_fixture_runtime_evidence`, `wine_proton_fixture_wine_gates`, `wine_proton_readiness_gate`, `wine_proton_runtime_gate`, `wine_proton_runtime_readiness_gate` | `common.wine_proton_gate`, `common.wine_proton_runtime` |
| `test/feature/usage/llvm_backend_spec.spl` (L52) | 7 | `LlvmIRBuilder__create`, `LlvmTargetConfig__compatibility_build`, `LlvmTargetConfig__for_target`, `LlvmTargetTriple__from_target`, `LlvmTargetTriple__from_target_with_mode`, `LlvmTypeMapper__create_for_target`, `MirToLlvm__create` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| `test/system/app/simpleos/feature/simpleos_proton_substrate_spec.spl` (L1) | 7 | `wine_proton_feature_gate`, `wine_proton_fixture_features`, `wine_proton_fixture_runtime_evidence`, `wine_proton_fixture_wine_gates`, `wine_proton_readiness_gate`, `wine_proton_runtime_gate`, `wine_proton_runtime_readiness_gate` | `common.wine_proton_gate`, `common.wine_proton_runtime` |
| `test/unit/app/ui/async_ui_spec.spl` (L12) | 6 | `AsyncUIState`, `dispatch_focus_next`, `dispatch_focus_prev`, `dispatch_quit`, `get_current_mode`, `new_async_state` | `common.ui.async_state` |
| `test/unit/hardware/rv32imac/rv32_compressed_spec.spl` (L16) | 6 | `decode_imm_i`, `decode_opcode`, `decode_rd`, `decode_rs1`, `decompress_rvc`, `rvc_reg` | `hardware.rv32imac.core.rv32_compressed`, `hardware.rv32imac.core.rv32_decode` |
| `test/unit/hardware/rv64gc/rv64_fp_compare_d_spec.spl` (L18) | 6 | `fp_class_d`, `fp_eq_d`, `fp_le_d`, `fp_lt_d`, `fp_max_d`, `fp_min_d` | `hardware.rv64gc.ext.rv64_double` |
| `test/unit/hardware/rv64gc/rv64_fp_compare_s_spec.spl` (L18) | 6 | `fp_class_s`, `fp_eq_s`, `fp_le_s`, `fp_lt_s`, `fp_max_s`, `fp_min_s` | `hardware.rv64gc.ext.rv64_float` |
| `test/unit/lib/blink/input_event_spec.spl` (L17) | 6 | `ModifierFlags`, `TouchPoint`, `char_event`, `mouse_event`, `touch_event`, `touch_point` | `std.blink.input.event` |
| `test/unit/lib/common/wine_proton_gate_spec.spl` (L1) | 6 | `wine_proton_feature_gate`, `wine_proton_fixture_features`, `wine_proton_fixture_wine_gates`, `wine_proton_missing_features`, `wine_proton_readiness_gate`, `wine_proton_required_features` | `common.wine_proton_gate` |
| `test/unit/lib/common/wine_proton_runtime_spec.spl` (L1) | 6 | `wine_proton_fixture_runtime_evidence`, `wine_proton_fixture_wine_gates`, `wine_proton_runtime_evidence_new`, `wine_proton_runtime_feature_evidence`, `wine_proton_runtime_gate`, `wine_proton_runtime_readiness_gate` | `common.wine_proton_gate`, `common.wine_proton_runtime` |
| `test/unit/lib_standalone/blink/input_event_spec.spl` (L17) | 6 | `ModifierFlags`, `TouchPoint`, `char_event`, `mouse_event`, `touch_event`, `touch_point` | `std.blink.input.event` |
| `test/unit/lib_standalone/common/wine_proton_gate_spec.spl` (L1) | 6 | `wine_proton_feature_gate`, `wine_proton_fixture_features`, `wine_proton_fixture_wine_gates`, `wine_proton_missing_features`, `wine_proton_readiness_gate`, `wine_proton_required_features` | `common.wine_proton_gate` |
| `test/unit/lib_standalone/common/wine_proton_runtime_spec.spl` (L1) | 6 | `wine_proton_fixture_runtime_evidence`, `wine_proton_fixture_wine_gates`, `wine_proton_runtime_evidence_new`, `wine_proton_runtime_feature_evidence`, `wine_proton_runtime_gate`, `wine_proton_runtime_readiness_gate` | `common.wine_proton_gate`, `common.wine_proton_runtime` |
| `test/feature/usage/llvm_backend_aarch64_spec.spl` (L13) | 6 | `LlvmIRBuilder__create`, `LlvmTargetConfig__for_target`, `LlvmTargetTriple__from_target`, `LlvmTargetTriple__from_target_baremetal`, `LlvmTypeMapper__create_for_target`, `MirToLlvm__create` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| `test/feature/usage/llvm_backend_i686_spec.spl` (L14) | 6 | `LlvmIRBuilder__create`, `LlvmTargetConfig__compatibility_build`, `LlvmTargetConfig__for_target`, `LlvmTargetTriple__from_target`, `LlvmTypeMapper__create_for_target`, `MirToLlvm__create` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| `test/03_system/os/boot_dbfs_kv_spec.spl` (L128) | 6 | `BootDbfsKvStore`, `boot_dbfs_kv_available`, `boot_dbfs_kv_clear`, `boot_dbfs_kv_get_if_mounted`, `boot_dbfs_kv_mount`, `boot_dbfs_kv_put_if_mounted` | `os.kernel.boot.boot_dbfs_kv` |
| `test/unit/app/build/feature_flags_spec.spl` (L4) | 5 | `FeatureFlag`, `apply_feature_overrides_aarch64`, `apply_feature_overrides_rv64`, `apply_feature_overrides_x86`, `parse_target_features` | `app.build.feature_flags` |
| `test/unit/app/build/opt_remarks_spec.spl` (L4) | 5 | `OptRemarkConfig`, `emit_cipher_remark`, `emit_cipher_remark_if`, `opt_remark_config_disabled`, `parse_opt_remarks` | `app.build.opt_remarks` |
| `test/unit/doc/riscv_fpga_bug_tracking_spec.spl` (L27) | 5 | `RiscvFpgaBugEntry`, `make_riscv_fpga_bug_entry`, `riscv_fpga_bug_doc_path`, `riscv_fpga_bug_entry_template`, `riscv_fpga_bug_id_prefix` | `doc.bugs.riscv_fpga_bug_convention` |
| `test/unit/hardware/rv64gc/rv64_alu_imm_spec.spl` (L18) | 5 | `alu_execute`, `alu_execute_word`, `decode_imm_i`, `decode_imm_u`, `decode_opcode` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute` |
| `test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl` (L18) | 5 | `fp_add_d`, `fp_div_d`, `fp_mul_d`, `fp_sqrt_d`, `fp_sub_d` | `hardware.rv64gc.ext.rv64_double` |
| `test/unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl` (L18) | 5 | `fp_add_s`, `fp_div_s`, `fp_mul_s`, `fp_sqrt_s`, `fp_sub_s` | `hardware.rv64gc.ext.rv64_float` |
| `test/unit/lib/blink/paint_chunk_spec.spl` (L18) | 5 | `PaintChunk`, `PaintChunkId`, `PropertyTreeState`, `paint_chunk_new`, `property_tree_state_root` | `std.blink.entity.paint_chunk` |
| `test/unit/lib/blink/scroll_manager_spec.spl` (L15) | 5 | `OverflowBehavior`, `ScrollManager`, `ScrollableArea`, `scroll_manager_new`, `scrollable_area_new` | `std.blink.scroll.manager` |
| `test/unit/lib/cc/tile_spec.spl` (L4) | 5 | `TileDrawState`, `TileId`, `TilePriority`, `tile_id_new`, `tile_new` | `std.lib.cc.entity.tile` |
| `test/unit/lib/common/wine_rtl_string_spec.spl` (L1) | 5 | `wine_rtl_execute_string`, `wine_rtl_free_ansi_string`, `wine_rtl_init_unicode_string`, `wine_rtl_string_required_calls`, `wine_rtl_unicode_string_to_ansi_string` | `common.wine_rtl_string` |
| `test/unit/lib/math/field/fe_p256_full_spec.spl` (L25) | 5 | `FeP256`, `fe_cond_select`, `fe_cond_swap`, `fe_is_zero`, `fe_pow` | `std.common.math.field.fe_p256` |
| `test/unit/lib_standalone/blink/paint_chunk_spec.spl` (L18) | 5 | `PaintChunk`, `PaintChunkId`, `PropertyTreeState`, `paint_chunk_new`, `property_tree_state_root` | `std.blink.entity.paint_chunk` |
| `test/unit/lib_standalone/blink/scroll_manager_spec.spl` (L15) | 5 | `OverflowBehavior`, `ScrollManager`, `ScrollableArea`, `scroll_manager_new`, `scrollable_area_new` | `std.blink.scroll.manager` |
| `test/unit/lib_standalone/cc/tile_spec.spl` (L4) | 5 | `TileDrawState`, `TileId`, `TilePriority`, `tile_id_new`, `tile_new` | `std.lib.cc.entity.tile` |
| `test/unit/lib_standalone/common/wine_rtl_string_spec.spl` (L1) | 5 | `wine_rtl_execute_string`, `wine_rtl_free_ansi_string`, `wine_rtl_init_unicode_string`, `wine_rtl_string_required_calls`, `wine_rtl_unicode_string_to_ansi_string` | `common.wine_rtl_string` |
| `test/integration/baremetal/baremetal_build_spec.spl` (L10) | 5 | `BaremetalBuilder`, `BaremetalConfig`, `baremetal_config_arm`, `baremetal_config_riscv`, `baremetal_config_x86_64` | `app.build.baremetal` |
| `test/integration/hardware/rv32imac/rv32_compliance_spec.spl` (L23) | 5 | `AluOp`, `AmoOp`, `MulDivOp`, `ReservationSet64`, `amo_execute` | `hardware.riscv_common.pkg.riscv_types_pkg`, `hardware.rv64gc.ext.rv64_atomics` |
| `test/integration/hardware/rv64gc/rv64_compliance_spec.spl` (L18) | 5 | `AmoOp`, `alu_execute`, `alu_execute_word`, `amo_execute`, `muldiv_execute_word` | `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, `hardware.rv64gc.ext.rv64_muldiv` |
| `test/integration/rendering/simd_parity_spec.spl` (L26) | 5 | `X86SimdGate`, `x86_simd_gate_allows_avx2`, `x86_simd_gate_allows_sse2`, `x86_simd_gate_any_enabled`, `x86_simd_gate_from_triple` | `compiler.backend.native.x86_64_simd` |
| `test/feature/app/t32_tools/t32_mcp_bugfix_spec.spl` (L27) | 5 | `t32_has_shell_meta`, `t32_is_all_digits`, `t32_is_hex_address`, `t32_shell_escape`, `t32_validate_identifier` | `app.mcp_t32.protocol` |
| `test/feature/usage/llvm_backend_arm32_spec.spl` (L13) | 5 | `LlvmIRBuilder__create`, `LlvmTargetConfig__for_target`, `LlvmTargetTriple__from_target`, `LlvmTypeMapper__create_for_target`, `MirToLlvm__create` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| `test/feature/usage/llvm_backend_riscv32_spec.spl` (L13) | 5 | `LlvmIRBuilder__create`, `LlvmTargetConfig__for_target`, `LlvmTargetTriple__from_target`, `LlvmTypeMapper__create_for_target`, `MirToLlvm__create` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| `test/feature/usage/llvm_backend_riscv64_spec.spl` (L13) | 5 | `LlvmIRBuilder__create`, `LlvmTargetConfig__for_target`, `LlvmTargetTriple__from_target`, `LlvmTypeMapper__create_for_target`, `MirToLlvm__create` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| `test/unit/doc/de10nano_quartus_setup_spec.spl` (L23) | 4 | `de10nano_device_string`, `litex_de10nano_build_command`, `quartus_lite_version`, `quartus_setup_guide_content` | `doc.fpga.de10nano_quartus_setup` |
| `test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl` (L18) | 4 | `fp_fmadd_d`, `fp_fmsub_d`, `fp_fnmadd_d`, `fp_fnmsub_d` | `hardware.rv64gc.ext.rv64_double` |
| `test/unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl` (L18) | 4 | `fp_fmadd_s`, `fp_fmsub_s`, `fp_fnmadd_s`, `fp_fnmsub_s` | `hardware.rv64gc.ext.rv64_float` |
| `test/unit/lib/blink/block_flow_spec.spl` (L16) | 4 | `BoxGeometry`, `box_geometry_new`, `box_geometry_zero`, `layout_box_new` | `std.blink.layout.block_flow` |
| `test/unit/lib/blink/navigation_controller_spec.spl` (L16) | 4 | `NavigationController`, `NavigationEntry`, `navigation_controller_new`, `navigation_entry_new` | `std.blink.navigation.controller` |
| `test/unit/lib/blink/style_cascade_spec.spl` (L21) | 4 | `computed_style_default`, `parse_f64_value`, `parse_length_value`, `resolve_style_with_state` | `std.blink.entity.computed_style`, `std.blink.style.cascade` |
| `test/unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl` (L2) | 4 | `SIMPLE_WEB_PARITY_CONVERTER`, `simple_web_rendering_parity_observe`, `simple_web_rendering_parity_paint_payload`, `simple_web_rendering_parity_stage_records` | `std.gc_async_mut.gpu.browser_engine.rendering_parity_adapter` |
| `test/unit/lib/math/field/fe25519_spec.spl` (L24) | 4 | `fe_cond_select`, `fe_cond_swap`, `fe_is_zero`, `fe_pow` | `std.common.math.field.fe25519` |
| `test/unit/lib_standalone/blink/block_flow_spec.spl` (L16) | 4 | `BoxGeometry`, `box_geometry_new`, `box_geometry_zero`, `layout_box_new` | `std.blink.layout.block_flow` |
| `test/unit/lib_standalone/blink/navigation_controller_spec.spl` (L16) | 4 | `NavigationController`, `NavigationEntry`, `navigation_controller_new`, `navigation_entry_new` | `std.blink.navigation.controller` |
| `test/unit/lib_standalone/blink/style_cascade_spec.spl` (L21) | 4 | `computed_style_default`, `parse_f64_value`, `parse_length_value`, `resolve_style_with_state` | `std.blink.entity.computed_style`, `std.blink.style.cascade` |
| `test/03_system/rv32imac_spec.spl` (L8) | 4 | `AluOp`, `ForwardSrc`, `MemOp`, `rvc_reg` | `hardware.riscv_common.core.riscv_compressed`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| `test/03_system/hardware/rv32imac_spec.spl` (L8) | 4 | `AluOp`, `ForwardSrc`, `MemOp`, `rvc_reg` | `hardware.riscv_common.core.riscv_compressed`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| `test/03_system/os/kernel/boot_fs_mount_spec.spl` (L143) | 4 | `boot_dbfs_kv_available`, `boot_dbfs_kv_clear`, `boot_dbfs_kv_get_if_mounted`, `boot_dbfs_kv_put_if_mounted` | `os.kernel.boot.boot_dbfs_kv` |
| `test/05_perf/tauri_equiv/simple_app.spl` (L18) | 4 | `event_loop_create`, `event_loop_is_valid`, `window_hide`, `window_show` | `nogc_sync_mut.io.window_ffi` |
| `test/perf/tauri_equiv/simple_app.spl` (L18) | 4 | `event_loop_create`, `event_loop_is_valid`, `window_hide`, `window_show` | `nogc_sync_mut.io.window_ffi` |
| `test/system/rv32imac_spec.spl` (L8) | 4 | `AluOp`, `ForwardSrc`, `MemOp`, `rvc_reg` | `hardware.riscv_common.core.riscv_compressed`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| `test/unit/compiler/backend/layout_scanner_spec.spl` (L1) | 3 | `get_layout_for_struct`, `layout_scanner_reset`, `scan_layout_annotations` | `app.build` |
| `test/unit/compiler/mdsoc/pipeline_integration_spec.spl` (L216) | 3 | `CacheCheckStatus`, `CachePort`, `create_noop_cache_port` | `compiler.mdsoc.feature.cache.cache_port` |
| `test/unit/hardware/rv64gc/rv64_atomics_spec.spl` (L18) | 3 | `AmoOp`, `ReservationSet64`, `amo_execute` | `hardware.rv64gc.ext.rv64_atomics` |
| `test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl` (L18) | 3 | `fp_sgnj_s`, `fp_sgnjn_s`, `fp_sgnjx_s` | `hardware.rv64gc.ext.rv64_float` |
| `test/unit/lib/blink/navigation_fetch_spec.spl` (L21) | 3 | `NavigationController`, `fetch_text`, `navigation_controller_new` | `std.blink.navigation.controller`, `std.blink.network.fetch` |
| `test/unit/lib/blink/paint_artifact_spec.spl` (L3) | 3 | `PaintArtifact`, `PaintChunk`, `PaintChunkProperties` | `std.blink.entity.paint_artifact` |
| `test/unit/lib/blink/url/url_parser_spec.spl` (L17) | 3 | `percent_decode`, `percent_encode`, `query_string_parse` | `std.blink.url.url_parser` |
| `test/unit/lib/cc/layer_base_spec.spl` (L6) | 3 | `LayerId`, `layer_id_new`, `layer_new` | `std.lib.cc.entity.layer_base` |
| `test/unit/lib/cc/property_tree_spec.spl` (L4) | 3 | `PropertyTrees`, `ScrollNode`, `property_trees_new` | `std.lib.cc.entity.property_tree` |
| `test/unit/lib/cc/tile_manager_spec.spl` (L4) | 3 | `RasterBufferProvider`, `TileKey`, `TilePriority` | `std.cc.entity.tile`, `std.cc.feature.raster_buffer_provider` |
| `test/unit/lib/common/units/generators/world_units_importers_spec.spl` (L1) | 3 | `import_all_world_unit_seed_rows`, `imported_rows_have_unique_ids`, `imported_rows_to_sdn` | `std.common.units.generators.world_units_importers` |
| `test/unit/lib/debug/remote/t32_ffi/t32_version_detect_spec.spl` (L3) | 3 | `T32ApiInfo`, `t32_execute_function_names`, `t32_notify_function_names` | `std.debug.remote.t32_ffi.t32_execute`, `std.debug.remote.t32_ffi.t32_notify`, `std.debug.remote.t32_ffi.t32_version_detect` |
| `test/unit/lib/mcp/lazy_loading_spec.spl` (L3) | 3 | `call_cached_handler`, `get_cached_handler`, `register_cached_handler` | `mcp_lib.lazy_registry` |
| `test/unit/lib/unit/unit_composite_spec.spl` (L26) | 3 | `Wh`, `kmph`, `mps` | `unit.energy`, `unit.velocity` |
| `test/unit/lib_standalone/blink/navigation_fetch_spec.spl` (L21) | 3 | `NavigationController`, `fetch_text`, `navigation_controller_new` | `std.blink.navigation.controller`, `std.blink.network.fetch` |
| `test/unit/lib_standalone/blink/paint_artifact_spec.spl` (L3) | 3 | `PaintArtifact`, `PaintChunk`, `PaintChunkProperties` | `std.blink.entity.paint_artifact` |
| `test/unit/lib_standalone/blink/url/url_parser_spec.spl` (L17) | 3 | `percent_decode`, `percent_encode`, `query_string_parse` | `std.blink.url.url_parser` |
| `test/unit/lib_standalone/cc/layer_base_spec.spl` (L6) | 3 | `LayerId`, `layer_id_new`, `layer_new` | `std.lib.cc.entity.layer_base` |
| `test/unit/lib_standalone/cc/property_tree_spec.spl` (L4) | 3 | `PropertyTrees`, `ScrollNode`, `property_trees_new` | `std.lib.cc.entity.property_tree` |
| `test/unit/lib_standalone/cc/tile_manager_spec.spl` (L4) | 3 | `RasterBufferProvider`, `TileKey`, `TilePriority` | `std.cc.entity.tile`, `std.cc.feature.raster_buffer_provider` |
| `test/unit/std/parser/treesitter_node_spec.spl` (L13) | 3 | `node_byte_range`, `node_is_valid`, `node_line_range` | `std.parser.treesitter_node` |
| `test/integration/rv32_multi_backend_boot_spec.spl` (L16) | 3 | `HybridSimulator`, `SimMode`, `encode_ebreak` | `test.helpers.riscv_encode`, `timing.hybrid_sim`, `timing.types` |
| `test/03_system/core/sys/wm_compare/v1_v2_parity_spec.spl` (L18) | 3 | `render_v1`, `render_v2`, `run_parity` | `app.wm_compare.v1_v2_parity` |
| `test/03_system/core/sys/wm_compare/v1_v3_parity_spec.spl` (L27) | 3 | `render_v1`, `render_v3`, `run_parity_v3` | `app.wm_compare.v1_v2_parity` |
| `test/03_system/core/sys/wm_compare/v1_v4_parity_spec.spl` (L28) | 3 | `render_v1`, `render_v4`, `run_parity_v4` | `app.wm_compare.v1_v2_parity` |
| `test/03_system/os/simpleos_riscv_network_gate_spec.spl` (L4) | 3 | `host_env_get`, `host_file_read_text`, `host_process_run_timeout` | `std.nogc_sync_mut.host.runtime_facade` |
| `test/unit/app/build/ffi_routing_spec.spl` (L11) | 2 | `default_ffi_build_config`, `parse_ffi_build_args` | `app.build.config` |
| `test/unit/compiler/ffi_gen/backend_gating_spec.spl` (L8) | 2 | `ffi_backend_not_implemented_message`, `ffi_backend_supported` | `compiler.tools.ffi_gen.main` |
| `test/unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl` (L18) | 2 | `AmoOrdering`, `decode_amo_ordering` | `hardware.rv64gc.ext.rv64_atomics` |
| `test/unit/hardware/rv64gc/rv64_compressed_spec.spl` (L17) | 2 | `decompress_rvc`, `rvc_reg` | `hardware.rv64gc.core.rv64_compressed` |
| `test/unit/lib/blink/html_tokenizer_spec.spl` (L19) | 2 | `HtmlAttribute`, `tokenize_html` | `std.blink.html_parser` |
| `test/unit/lib/blink/html_tree_builder_spec.spl` (L19) | 2 | `HtmlAttribute`, `build_html_tree` | `std.blink.html_parser`, `std.blink.html_parser.tree_builder` |
| `test/unit/lib/blink/paint_controller_spec.spl` (L3) | 2 | `PaintChunkProperties`, `PaintController` | `std.blink.entity.paint_artifact`, `std.blink.feature.paint.paint_controller` |
| `test/unit/lib/cc/layer_tree_host_spec.spl` (L5) | 2 | `LayerTreeHost`, `LayerTreeImpl` | `std.cc.entity.layer_tree_host` |
| `test/unit/lib/cc/picture_layer_impl_spec.spl` (L5) | 2 | `PictureLayerImpl`, `RasterSource` | `std.cc.feature.picture_layer_impl`, `std.cc.feature.raster_source` |
| `test/unit/lib/common/immut/combinators_spec.spl` (L7) | 2 | `Pipeline__new`, `Pipeline__of` | `lib.combinators.pipeline` |
| `test/unit/lib/common/units/engine/unit_expr_spec.spl` (L1) | 2 | `format_unit_expression`, `parse_unit_expression` | `std.common.units.engine.unit_expr` |
| `test/unit/lib/immut/combinators_spec.spl` (L7) | 2 | `Pipeline__new`, `Pipeline__of` | `std.combinators.pipeline` |
| `test/unit/lib/std/game_engine/effects_spec.spl` (L5) | 2 | `EffectContext`, `GameEffect` | `std.game_engine.effects` |
| `test/unit/lib/unit/unit_literal_postfix_spec.spl` (L19) | 2 | `degC`, `kmph` | `unit.temperature`, `unit.velocity` |
| `test/unit/lib_standalone/blink/html_tokenizer_spec.spl` (L19) | 2 | `HtmlAttribute`, `tokenize_html` | `std.blink.html_parser` |
| `test/unit/lib_standalone/blink/html_tree_builder_spec.spl` (L19) | 2 | `HtmlAttribute`, `build_html_tree` | `std.blink.html_parser`, `std.blink.html_parser.tree_builder` |
| `test/unit/lib_standalone/blink/paint_controller_spec.spl` (L3) | 2 | `PaintChunkProperties`, `PaintController` | `std.blink.entity.paint_artifact`, `std.blink.feature.paint.paint_controller` |
| `test/unit/lib_standalone/cc/layer_tree_host_spec.spl` (L5) | 2 | `LayerTreeHost`, `LayerTreeImpl` | `std.cc.entity.layer_tree_host` |
| `test/unit/lib_standalone/cc/picture_layer_impl_spec.spl` (L5) | 2 | `PictureLayerImpl`, `RasterSource` | `std.cc.feature.picture_layer_impl`, `std.cc.feature.raster_source` |
| `test/unit/os/compositor/engine2d_render_evidence_spec.spl` (L36) | 2 | `render_capture_control_wire_byte_at`, `render_capture_control_wire_byte_count` | `os.kernel.arch.x86.render_capture_ack` |
| `test/unit/os/crypto/x25519mlkem768_absolute_spec.spl` (L35) | 2 | `CRYPTO_ENTROPY_MAX_REQUEST`, `crypto_entropy_validate_candidate_for_test` | `os.crypto.entropy` |
| `test/unit/specs/modules_spec.spl` (L89) | 2 | `Client`, `TlsStream` | `self.client`, `self.tls` |
| `test/integration/hardware/rv64gc/rv64_core_smoke_spec.spl` (L20) | 2 | `alu_execute`, `alu_execute_word` | `hardware.rv64gc.core.rv64_execute` |
| `test/integration/os/rv64_boot_spec.spl` (L22) | 2 | `alu_execute`, `alu_execute_word` | `hardware.rv64gc.core.rv64_execute` |
| `test/integration/rendering/effect_engine_compare_spec.spl` (L17) | 2 | `build_rendering_stress_html`, `generate_glass_test_html` | `common.ui.glass_test_page` |
| `test/integration/rendering/glass_render_e2e_spec.spl` (L13) | 2 | `build_rendering_stress_html`, `generate_glass_test_html` | `common.ui.glass_test_page` |
| `test/integration/rendering/pixel_verify_main.spl` (L10) | 2 | `build_rendering_stress_html`, `generate_glass_test_html` | `common.ui.glass_test_page` |
| `test/integration/rendering/pixel_verify_runner.spl` (L10) | 2 | `build_rendering_stress_html`, `generate_glass_test_html` | `common.ui.glass_test_page` |
| `test/feature/language/modules_spec.spl` (L89) | 2 | `Client`, `TlsStream` | `self.client`, `self.tls` |
| `test/03_system/lib/database/postgres_mimic_server_spec.spl` (L10) | 2 | `database_plan_uses_compiled_artifact`, `database_select_plan` | `std.database.deployment` |
| `test/03_system/os/db_server_integrated_stack_spec.spl` (L109) | 2 | `SimpleDbServer`, `register_db_server_routes` | `std.db.db_server` |
| `test/integration/rendering/backend_screenshot_compare_spec.spl` (L18) | 2 | `build_rendering_stress_html`, `generate_glass_test_html` | `common.ui.glass_test_page` |
| `test/unit/app/lifecycle_spec.spl` (L4) | 1 | `run_oneshot` | `nogc_sync_mut.src.app.runner` |
| `test/unit/app/test_daemon/test_daemon_session_config_spec.spl` (L15) | 1 | `parse_test_config_content` | `test_config` |
| `test/unit/app/ui/async_default_api_spec.spl` (L6) | 1 | `create_sync_backend` | `common.ui` |
| `test/unit/app/ui/unified_app_spec.spl` (L4) | 1 | `UnifiedApp` | `common.ui.app` |
| `test/unit/compiler/diagnostic_formatter_contract_spec.spl` (L3) | 1 | `SimpleFormatter` | `std.diagnostics.formatters` |
| `test/unit/compiler/wasm_codegen_spec.spl` (L8) | 1 | `WasmTypeMapper__create_wasm32` | `compiler.backend.wasm_type_mapper` |
| `test/unit/compiler/frontend/required_comment_parse_spec.spl` (L41) | 1 | `ast_expr_reset` | `compiler.core.ast_expr` |
| `test/unit/compiler/module_resolver/type_domain_resolver_spec.spl` (L9) | 1 | `normalize_type_segments` | `compiler.module_resolver.resolution` |
| `test/unit/lib/blink/computed_style_spec.spl` (L16) | 1 | `computed_style_default` | `std.blink.entity.computed_style` |
| `test/unit/lib/blink/document_spec.spl` (L16) | 1 | `document_new` | `std.blink.dom.document` |
| `test/unit/lib/common/immut/integration_spec.spl` (L13) | 1 | `Pipeline__new` | `lib.combinators.pipeline` |
| `test/unit/lib/content/web_contents_spec.spl` (L5) | 1 | `PaintArtifact` | `std.blink.entity.paint_artifact` |
| `test/unit/lib/immut/integration_spec.spl` (L13) | 1 | `Pipeline__new` | `std.combinators.pipeline` |
| `test/unit/lib/math/field/fe_p256_skeleton_spec.spl` (L16) | 1 | `FeP256` | `std.common.math.field.fe_p256` |
| `test/unit/lib/unit/unit_raw_warning_spec.spl` (L20) | 1 | `i32_to_km` | `unit.length` |
| `test/unit/lib_standalone/blink/computed_style_spec.spl` (L16) | 1 | `computed_style_default` | `std.blink.entity.computed_style` |
| `test/unit/lib_standalone/blink/document_spec.spl` (L16) | 1 | `document_new` | `std.blink.dom.document` |
| `test/unit/lib_standalone/content/web_contents_spec.spl` (L5) | 1 | `PaintArtifact` | `std.blink.entity.paint_artifact` |
| `test/unit/os/drivers/audio/hda_pcm_pack_spec.spl` (L3) | 1 | `pcm_i16_pack_4` | `std.common.audio.pcm_i16` |
| `test/unit/os/qemu/arm64_wm_shared_mdi_contract_spec.spl` (L4) | 1 | `arm64_wm_shared_mdi_evidence` | `examples.simple_os.arch.arm64.wm_shared_mdi_contract` |
| `test/integration/compiler/llvm_compiled_proof_spec.spl` (L31) | 1 | `LlvmTargetConfig__for_target` | `compiler.backend.llvm_target` |
| `test/integration/compiler/driver/effect_inference_wiring_spec.spl` (L9) | 1 | `run_effect_pass` | `compiler.types.type_system.effect_pass` |
| `test/integration/compiler/llvm_text_bitcode_debug_spec.spl` (L5) | 1 | `LlvmTargetConfig__for_target` | `compiler.backend.llvm_target` |
| `test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl` (L4) | 1 | `rv32_soc_create` | `hardware.rv32gc.top.rv32_soc` |
| `test/integration/hardware/rv32imac/rv32_hello_world_spec.spl` (L21) | 1 | `Rv32Uart` | `hardware.rv32gc.periph.rv32_uart` |
| `test/integration/rendering/glass_pipeline_screenshot_spec.spl` (L20) | 1 | `generate_glass_test_html` | `common.ui.glass_test_page` |
| `test/integration/rendering/pixel_verify_debug.spl` (L10) | 1 | `execute_scene_to_buffer` | `common.render_scene.executor` |
| `test/integration/rendering/pixel_verify_dom_render.spl` (L20) | 1 | `execute_scene_to_buffer` | `common.render_scene.executor` |
| `test/integration/rendering/pixel_verify_full.spl` (L12) | 1 | `execute_scene_to_buffer` | `common.render_scene.executor` |
| `test/integration/rendering/pixel_verify_minimal.spl` (L8) | 1 | `execute_scene_to_buffer` | `common.render_scene.executor` |
| `test/integration/rendering/pixel_verify_scene.spl` (L12) | 1 | `execute_scene_to_buffer` | `common.render_scene.executor` |
| `test/03_system/command_history_spec.spl` (L7) | 1 | `CommandMeta` | `std.common.command.command` |
| `test/03_system/os_rt_rsa_pss_verify_spec.spl` (L29) | 1 | `rsa_pss_sha384_verify` | `std.nogc_sync_mut.io.signature_ffi` |
| `test/03_system/unit_system_integration_spec.spl` (L19) | 1 | `kmph` | `unit.velocity` |
| `test/03_system/core/sys/wm_compare/golden_gate_spec.spl` (L30) | 1 | `render_v1` | `app.wm_compare.v1_v2_parity` |
| `test/03_system/e2e/unit_system_integration_spec.spl` (L19) | 1 | `kmph` | `unit.velocity` |
| `test/feature/app/t32_tools/t32_mcp_spec.spl` (L21) | 1 | `t32_make_tool_schema` | `app.mcp_t32.protocol` |
| `test/feature/usage/wasm_compile_spec.spl` (L37) | 1 | `WasmTypeMapper__create_wasm32` | `compiler.backend.wasm_type_mapper` |
| `test/03_system/gui/command_history_spec.spl` (L7) | 1 | `CommandMeta` | `std.common.command.command` |
| `test/03_system/gui/unified_app_spec.spl` (L33) | 1 | `UnifiedApp` | `common.ui.app` |
| `test/cert/tool_qual/negative/06_undefined_module_import.spl` (L4) | 1 | `thing` | `std.no_such_module_xyz` |
| `test/system/command_history_spec.spl` (L7) | 1 | `CommandMeta` | `std.common.command.command` |
| `test/system/gui/unified_app_spec.spl` (L6) | 1 | `UnifiedApp` | `common.ui.app` |
| `test/system/os_rt_rsa_pss_verify_spec.spl` (L29) | 1 | `rsa_pss_sha384_verify` | `std.nogc_sync_mut.io.signature_ffi` |
| `test/system/unit_system_integration_spec.spl` (L19) | 1 | `kmph` | `unit.velocity` |

### B.2 LIVE-AND-BROKEN — 308 entries across 107 specs

| spec (canonical) | n | undeclared names | modules |
|---|---|---|---|
| `test/unit/app/t32_cli/error_codes_spec.spl` (L3) | 27 | `T4001`, `T4002`, `T4003`, `T4013`, `T4030`, `T4060`, `T4070`, `T4080`, `T4081`, `T4082`, `T4090`, `t32_did_you_mean`, `t32_err_catalog_warning`, `t32_err_missing_args`, `t32_err_missing_param`, `t32_err_missing_tool_name`, `t32_err_no_session`, `t32_err_not_found`, `t32_err_resource_not_found`, `t32_err_session_closed`, `t32_err_session_duplicate`, `t32_err_t32rem_not_found`, `t32_err_unknown_cmd`, `t32_err_unknown_ … | `app.t32_cli.error_codes` |
| `test/feature/app/t32_tools/t32_mcp_spec.spl` (L20) | 18 | `t32_LB`, `t32_Q`, `t32_RB`, `t32_escape_json`, `t32_extract_field`, `t32_extract_field_raw`, `t32_extract_id`, `t32_extract_nested`, `t32_jo1`, `t32_jo2`, `t32_jo3`, `t32_jo4`, `t32_jp`, `t32_js`, `t32_make_error`, `t32_make_json_result`, `t32_make_tool_error`, `t32_make_tool_result` | `app.mcp_t32.json_helpers` |
| `test/unit/app/t32_cli/access_cli_grammar_spec.spl` (L3) | 17 | `MCP_T32_HISTORY`, `T32BridgeResult`, `T32_ACTION_ARG_MAX_LENGTH`, `bridge_action_invoke`, `bridge_history_tail`, `bridge_window_list`, `find_shared_access_command`, `prepare_access_args`, `shared_access_commands`, `t32_action_command`, `t32_action_request_id`, `t32_add_history_with_request`, `t32_cli_main`, `t32_find_action`, `t32_get_window_actions`, `t32_map_access_error`, `t32_run_remote_process` | `app.mcp_t32.session_state`, `app.mcp_t32.session_tools`, `app.mcp_t32.window_tools`, `app.t32_cli.bridge`, `app.t32_cli.bridge_access`, `app.t32_cli.commands`, `app.t32_cli.mod`, `app.t32_cli.types` |
| `test/unit/lib/debug/remote/t32_ffi/t32_types_spec.spl` (L3) | 15 | `T32_DEV_ICD`, `T32_ERR_ATTACH_FAIL`, `T32_ERR_COM_RECEIVE_FAIL`, `T32_ERR_COM_RECEIVE_TIMEOUT`, `T32_ERR_COM_TRANSMIT_FAIL`, `T32_ERR_FAIL`, `T32_ERR_NOMEMORY`, `T32_GROUP_CORE`, `T32_GROUP_EXECUTE`, `T32_REG_OBJ_R32`, `T32_REG_OBJ_R64`, `T32_STATE_DOWN`, `T32_STATE_HALTED`, `T32_STATE_RUNNING`, `t32_error_message` | `std.debug.remote.t32_ffi.t32_types` |
| `test/feature/app/t32_tools/t32_cli_spec.spl` (L23) | 14 | `T32Action`, `T32Catalogs`, `T32Field`, `T32WindowNode`, `cli_commands`, `parse_tabular_output`, `split_on`, `t32_did_you_mean`, `t32_err_no_session`, `t32_err_session_duplicate`, `t32_err_session_not_found`, `t32_err_unknown_cmd`, `t32_join_list`, `t32_suggest_similar` | `app.t32_cli.error_codes`, `app.t32_cli.text_parser`, `app.t32_cli.types` |
| `test/unit/app/t32_cli/error_messages_spec.spl` (L3) | 12 | `cli_sessions_subcmds`, `t32_err_action_not_found`, `t32_err_cmd_failed`, `t32_err_core_not_found`, `t32_err_field_not_found`, `t32_err_no_session_mcp`, `t32_err_not_found`, `t32_err_session_not_found`, `t32_err_unknown_cmd`, `t32_err_unknown_shell_cmd`, `t32_err_unknown_subcmd`, `t32_err_window_not_found` | `app.t32_cli.error_codes` |
| `test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl` (L3) | 12 | `RISCV_ECALL_INSTR`, `RISCV_PRIV_MACHINE`, `RISCV_PRIV_SUPERVISOR`, `RISCV_PRIV_USER`, `RV64_DEBUG_WRITE_ECALL_PC`, `RV64_DEBUG_WRITE_RESUME_PC`, `RiscvFormalContract`, `RiscvRetireEvent`, `riscv_instruction_size`, `riscv_mask_for_xlen`, `verify_riscv_event`, `verify_riscv_events` | `hardware.riscv_common.core.riscv_formal` |
| `test/feature/app/t32_tools/t32_mcp_tools_spec.spl` (L22) | 11 | `t32_build_cmm_command_db`, `t32_field_to_eval`, `t32_field_to_set_cmd`, `t32_hardcoded_window_catalog`, `t32_is_status_field`, `t32_normalize_current_status`, `t32_parse_window_sdn`, `t32_text_contains`, `t32_to_lower`, `t32_toolbar_run_enabled`, `t32_toolbar_stop_enabled` | `app.mcp_t32.action_tools`, `app.mcp_t32.headless_tools`, `app.mcp_t32.window_tools` |
| `test/unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl` (L6) | 10 | `css_get_flex_direction`, `css_get_flex_wrap`, `css_get_list_style_type`, `css_get_outline_color`, `css_get_outline_offset`, `css_get_outline_style`, `css_get_outline_width`, `css_get_width`, `css_value_as_i32`, `css_value_unit` | `std.gc_async_mut.gpu.browser_engine.css` |
| `test/unit/browser/script/navigator_api_spec.spl` (L2) | 7 | `navigator_gpu_adapter_available`, `navigator_gpu_adapter_request_device`, `navigator_gpu_bridge`, `navigator_gpu_preferred_canvas_format`, `navigator_gpu_request_adapter`, `navigator_gpu_request_adapter_status`, `navigator_gpu_secure_context` | `std.gc_async_mut.gpu.browser_engine.script.navigator_api` |
| `test/unit/lib/common/proton_runtime_subsystems_spec.spl` (L1) | 6 | `proton_graphics_translation_gate`, `proton_non_wine_runtime_evidence_new`, `proton_pressure_vessel_gate`, `proton_steam_integration_gate`, `proton_steam_runtime_gate`, `proton_sync_gate` | `common.proton_runtime_subsystems` |
| `test/unit/lib_standalone/common/proton_runtime_subsystems_spec.spl` (L1) | 6 | `proton_graphics_translation_gate`, `proton_non_wine_runtime_evidence_new`, `proton_pressure_vessel_gate`, `proton_steam_integration_gate`, `proton_steam_runtime_gate`, `proton_sync_gate` | `common.proton_runtime_subsystems` |
| `test/unit/app/t32_cli/t32_cli_commands_spec.spl` (L3) | 5 | `all_mcp_tool_names`, `all_shell_verbs`, `all_top_level_names`, `find_cli_command`, `subcmds_for` | `app.t32_cli.commands` |
| `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl` (L5) | 5 | `hit_test_dispatch_click`, `hit_test_dispatch_pointer_activation`, `hit_test_dispatch_pointer_event`, `hit_test_dispatch_pointer_event_with_modifiers`, `hit_test_path` | `std.gc_async_mut.gpu.browser_engine.layout` |
| `test/fixtures/native_mir_local_projection/main.spl` (L1) | 5 | `mir_function_local_type`, `mir_local_storage_alignment`, `mir_local_storage_size`, `mir_type_integer_width_bytes`, `mir_type_storage_size` | `compiler.mir.mir_instructions`, `compiler.mir.mir_types` |
| `test/unit/app/ui/capability_policy_spec.spl` (L12) | 4 | `capability_to_string`, `default_deny_policy`, `deny_capability`, `grant_capability` | `std.common.ui.capability`, `std.common.ui.capability_policy` |
| `test/unit/lib/crypto/crypto_reference_spec.spl` (L4) | 4 | `get_recommended_pbkdf2_iterations`, `md5_hex`, `pbkdf2_sha512`, `pbkdf2_with_algorithm` | `std.crypto.legacy_hash`, `std.crypto.pbkdf2` |
| `test/unit/os/apps/terminal/terminal_spec.spl` (L2) | 4 | `AnsiState`, `TerminalChar`, `TerminalLine`, `default_char` | `os.apps.terminal.terminal` |
| `test/feature/app/t32_tools/t32_lsp_mcp_spec.spl` (L22) | 4 | `lsp_escape_json`, `lsp_jo1`, `lsp_jp`, `lsp_js` | `app.t32_lsp_mcp.json_helpers` |
| `test/feature/app/t32_tools/t32_mcp_bugfix_spec.spl` (L28) | 4 | `t32_field_state_get`, `t32_field_state_set`, `t32_field_to_eval`, `t32_field_to_set_cmd` | `app.mcp_t32.action_tools` |
| `test/unit/lib/engine/units_spec.spl` (L9) | 3 | `FrameIndex`, `GamepadButtonId`, `PixelSize` | `std.common.engine.units` |
| `test/unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl` (L23) | 3 | `K26VexRiscvSocConfig`, `generate_k26_soc_top_vexriscv`, `k26_vexriscv_soc_config` | `lib.hardware.fpga_k26.k26_soc_top` |
| `test/unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl` (L24) | 3 | `add_verilog_sources`, `enable_axi_hp_port`, `synthesis_project_default` | `lib.hardware.fpga_linux.synthesis_wrapper` |
| `test/unit/lib/http_server/rate_limit_spec.spl` (L12) | 3 | `check_rate_limit`, `default_rate_limit_config`, `new_rate_limit_store` | `std.http_server.rate_limit` |
| `test/unit/lib/http_server/request_validation_spec.spl` (L12) | 3 | `default_max_uri_length`, `validate_request_path`, `validate_uri_length` | `std.http_server.request_validation` |
| `test/unit/lib/nogc_async_mut_noalloc/log/logger_spec.spl` (L2) | 3 | `_log_policy_allows`, `_normalize_prefixed_message`, `simple_log_c_enabled` | `lib.nogc_async_mut_noalloc.log` |
| `test/05_perf/bench/http_range_bench.spl` (L14) | 3 | `tcp_backend_connect`, `tcp_backend_read_text`, `tcp_backend_write_text` | `std.nogc_sync_mut.io.tcp` |
| `test/integration/rendering/backend_screenshot_compare_spec.spl` (L11) | 3 | `BackendCompareEntry`, `capture_all_available`, `print_multi_backend_report` | `os.compositor.screenshot_compare`, `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture` |
| `test/perf/bench/http_range_bench.spl` (L14) | 3 | `tcp_backend_connect`, `tcp_backend_read_text`, `tcp_backend_write_text` | `std.nogc_sync_mut.io.tcp` |
| `test/unit/app/build/ffi_routing_spec.spl` (L9) | 2 | `ffi_gen_entry_path`, `ffi_gen_force_args` | `app.io.cli_commands` |
| `test/unit/app/ui.chromium/css_spec.spl` (L32) | 2 | `css_get_flex_direction`, `css_get_gap` | `std.gc_async_mut.gpu.browser_engine.css` |
| `test/unit/compiler/mir_opt/collection_opt_spec.spl` (L3) | 2 | `collection_opt_optimize_function`, `mir_type_is_text` | `compiler.mir.mir_types`, `compiler.mir_opt.mir_opt.collection_opt` |
| `test/unit/lib/blink/css_selector_spec.spl` (L23) | 2 | `attribute_new`, `dom_node_new` | `std.blink.dom.node` |
| `test/unit/lib/http_server/csrf_spec.spl` (L12) | 2 | `is_csrf_exempt_method`, `validate_csrf_token` | `std.http_server.csrf` |
| `test/unit/lib/http_server/security_headers_spec.spl` (L12) | 2 | `build_security_header_value`, `default_security_headers_config` | `std.http_server.security_headers` |
| `test/unit/lib/nogc_sync_mut/engine/render/shader_compile_spec.spl` (L2) | 2 | `shader_compiler_get_or_compile_spirv`, `shader_compiler_get_or_compile_wgsl` | `std.nogc_sync_mut.engine.render.shader_compile` |
| `test/unit/lib_standalone/blink/css_selector_spec.spl` (L23) | 2 | `attribute_new`, `dom_node_new` | `std.blink.dom.node` |
| `test/unit/lib_standalone/nogc_sync_mut/engine/render/shader_compile_spec.spl` (L2) | 2 | `shader_compiler_get_or_compile_spirv`, `shader_compiler_get_or_compile_wgsl` | `std.nogc_sync_mut.engine.render.shader_compile` |
| `test/unit/os/compositor/simple_web_window_renderer_spec.spl` (L3) | 2 | `render_simple_web_app_content`, `simple_web_app_html` | `os.compositor.simple_web_window_renderer` |
| `test/unit/os/kernel/timer_test.spl` (L25) | 2 | `TscCalSource`, `tsc_calibration_source` | `os.kernel.arch.x86_64.timer` |
| `test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl` (L7) | 2 | `OBSOLETE_GROUP_X25519_KYBER768_DRAFT00`, `OBSOLETE_GROUP_X25519_MLKEM768_DRAFT00` | `os.tls13.handshake13` |
| `test/unit/browser_engine/html_tree_builder_spec.spl` (L6) | 2 | `be_dom_get_attribute`, `be_dom_get_tag_name` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| `test/unit/app/cli/cli_os_spec.spl` (L2) | 1 | `handle_os_inline` | `app.cli.main` |
| `test/unit/app/t32_cli/t32_cli_parity_guard_spec.spl` (L5) | 1 | `all_mcp_tool_names` | `app.t32_cli.commands` |
| `test/unit/app/tooling/test_result_wrapper_authored_count_spec.spl` (L2) | 1 | `count_authored_examples` | `std.test_runner.test_result_wrapper` |
| `test/unit/app/ui.chromium/text_metrics_spec.spl` (L9) | 1 | `browser_render_vector_font_probe_pixels` | `std.gc_async_mut.gpu.browser_engine.text_painter` |
| `test/unit/app/ui/shared_wm_entrypoints_spec.spl` (L8) | 1 | `_host_backend_selector` | `os.compositor.host_compositor_entry` |
| `test/unit/app_standalone/simple_process_manager/spm_service_spec.spl` (L20) | 1 | `window_record_encode` | `lib.common.win_fs.window_record` |
| `test/unit/browser/script/event_api_spec.spl` (L9) | 1 | `event_dispatch` | `std.gc_async_mut.gpu.browser_engine.script.event_api` |
| `test/unit/browser_engine/ifc_linebox_spec.spl` (L2) | 1 | `layout_inline` | `std.gc_async_mut.gpu.browser_engine.layout` |
| `test/unit/browser_engine/layout_text_node_spec.spl` (L5) | 1 | `layout_text_has_break_opportunity` | `std.gc_async_mut.gpu.browser_engine.layout_core` |
| `test/unit/browser_engine/table_layout_spec.spl` (L2) | 1 | `layout_table` | `std.gc_async_mut.gpu.browser_engine.layout` |
| `test/unit/browser_engine_standalone/ifc_linebox_spec.spl` (L2) | 1 | `layout_inline` | `std.gc_async_mut.gpu.browser_engine.layout` |
| `test/unit/browser_engine_standalone/layout_text_node_spec.spl` (L5) | 1 | `layout_text_has_break_opportunity` | `std.gc_async_mut.gpu.browser_engine.layout_core` |
| `test/unit/browser_engine_standalone/table_layout_spec.spl` (L2) | 1 | `layout_table` | `std.gc_async_mut.gpu.browser_engine.layout` |
| `test/unit/compiler/mdsoc/feature_ports_spec.spl` (L25) | 1 | `ArenaResidency` | `common.compute.placement_contracts.handles` |
| `test/unit/compiler/semantics/flat_imported_method_resolution_spec.spl` (L13) | 1 | `resolve_flat_methods` | `compiler.semantics.resolve` |
| `test/unit/lib/blink/dom_node_spec.spl` (L17) | 1 | `dom_tree_new` | `std.blink.dom.node` |
| `test/unit/lib/blink/style_cascade_spec.spl` (L16) | 1 | `dom_tree_new` | `std.blink.dom.node` |
| `test/unit/lib/common/proton_session_spec.spl` (L1) | 1 | `proton_non_wine_runtime_evidence_new` | `common.proton_runtime_subsystems` |
| `test/unit/lib/common/ui/theme_package_spec.spl` (L14) | 1 | `simple_web_app_html_with_theme` | `os.compositor.simple_web_window_renderer` |
| `test/unit/lib/common/win_fs/window_record_spec.spl` (L13) | 1 | `window_update_title` | `lib.common.win_fs.window_record` |
| `test/unit/lib/common/window_protocol/input_translator_spec.spl` (L5) | 1 | `WM_EVENT_KEY_PRESS` | `common.window_protocol.window_protocol` |
| `test/unit/lib/content/render_widget_host_view_spec.spl` (L8) | 1 | `InputEventKind` | `std.content.feature.render_widget_host_view` |
| `test/unit/lib/crypto/poly1305_spec.spl` (L19) | 1 | `poly1305_key_gen` | `std.crypto.poly1305` |
| `test/unit/lib/crypto/sha2_nist_vectors_spec.spl` (L17) | 1 | `sha512_hex` | `std.crypto.sha512` |
| `test/unit/lib/engine/device_spec.spl` (L7) | 1 | `preferred_graphics_backend` | `std.common.gpu.device` |
| `test/unit/lib/engine/ids_spec.spl` (L8) | 1 | `SpriteId` | `std.common.engine.ids` |
| `test/unit/lib/gpu/graphics_context_spec.spl` (L6) | 1 | `preferred_graphics_backend` | `std.common.gpu.device` |
| `test/unit/lib/gpu/engine2d/generated_kernel_args_spec.spl` (L14) | 1 | `GENERATED_2D_GLYPH` | `std.gc_async_mut.gpu.engine2d.generated_kernel_dispatch` |
| `test/unit/lib/gpu/engine2d/helpers_text_cache_spec.spl` (L5) | 1 | `TextBlitCache` | `std.gpu.engine2d.helpers_text` |
| `test/unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl` (L32) | 1 | `compile_to_vhdl_module` | `lib.hardware.fpga_linux.riscv_fpga_linux` |
| `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl` (L41) | 1 | `core64_step` | `std.hardware.rv64gc_rtl.core` |
| `test/unit/lib/hardware/rv64gc_rtl/.spipe_wrapped_entry_core64_integration_spec.spl` (L2) | 1 | `core64_step` | `std.hardware.rv64gc_rtl.core` |
| `test/unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl` (L2) | 1 | `nvme_arena_registered_count` | `std.nogc_sync_mut.db.dbfs_engine.raw_nvme_arena` |
| `test/unit/lib_standalone/blink/dom_node_spec.spl` (L17) | 1 | `dom_tree_new` | `std.blink.dom.node` |
| `test/unit/lib_standalone/blink/style_cascade_spec.spl` (L16) | 1 | `dom_tree_new` | `std.blink.dom.node` |
| `test/unit/lib_standalone/common/proton_session_spec.spl` (L1) | 1 | `proton_non_wine_runtime_evidence_new` | `common.proton_runtime_subsystems` |
| `test/unit/lib_standalone/common/win_fs/window_record_spec.spl` (L13) | 1 | `window_update_title` | `lib.common.win_fs.window_record` |
| `test/unit/lib_standalone/content/render_widget_host_view_spec.spl` (L8) | 1 | `InputEventKind` | `std.content.feature.render_widget_host_view` |
| `test/unit/os/qemu_runner_spec.spl` (L1) | 1 | `qemu_serial_reports_test_passed_without_failure` | `os.qemu_runner` |
| `test/unit/os/__tmp_adapter_probe.spl` (L9) | 1 | `_device_mapping` | `os.kernel.memory.memory_leveling_device_adapters` |
| `test/unit/os/apps/browser_demo_render_spec.spl` (L3) | 1 | `render_demo_to_pixels` | `os.apps.browser_demo.browser_demo` |
| `test/unit/os/apps/file_explorer/finder_spec.spl` (L20) | 1 | `simple_web_app_html_with_theme` | `os.compositor.simple_web_window_renderer` |
| `test/unit/os/apps/file_explorer/.spipe_wrapped_entry_finder_spec.spl` (L2) | 1 | `simple_web_app_html_with_theme` | `os.compositor.simple_web_window_renderer` |
| `test/unit/os/apps/smux/smux_app_spec.spl` (L12) | 1 | `smux_app_id` | `os.apps.smux.smux_remote` |
| `test/unit/os/compositor/.spipe_wrapped_entry_wm_action_applier_spec.spl` (L3) | 1 | `wm_action_web_window_request` | `os.compositor.wm_action_applier` |
| `test/unit/os/compositor/engine2d_render_evidence_spec.spl` (L35) | 1 | `FirmwareSha256` | `os.drivers.framebuffer.ramfb` |
| `test/unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl` (L5) | 1 | `render_shared_mdi_framebuffer_scene_for_taskbar_render_input` | `os.compositor.shared_mdi_framebuffer_scene` |
| `test/unit/os/compositor/wm_action_applier_spec.spl` (L11) | 1 | `wm_action_web_window_request` | `os.compositor.wm_action_applier` |
| `test/unit/os/drivers/audio/probe_hda_dma_resources.spl` (L1) | 1 | `hda_dma_write_pcm_i16` | `os.drivers.audio.hda_dma_resources` |
| `test/unit/os/kernel/arch/syscall_dispatch_spec.spl` (L10) | 1 | `expect_eq` | `std.spec` |
| `test/unit/os/shell/awk_spec.spl` (L44) | 1 | `AckProgram` | `os.tools.shell.awk.awk_tool` |
| `test/unit/os/shell/shell_script_spec.spl` (L45) | 1 | `ShellExpander` | `os.apps.shell.shell_expand` |
| `test/integration/app/simple_process_manager/spm_service_spec.spl` (L20) | 1 | `window_record_encode` | `lib.common.win_fs.window_record` |
| `test/integration/app/web/x25519mlkem768_web_browser_integration_spec.spl` (L22) | 1 | `tls_certificate_oid_is_ed25519` | `std.tls.certificate` |
| `test/integration/net/http_content_encoding_spec.spl` (L18) | 1 | `zlib_decompress` | `std.nogc_sync_mut.compression.zlib` |
| `test/integration/os/apps/sshd/ssh_aes256_gcm_packet_spec.spl` (L172) | 1 | `ssh_aes256_gcm_replay_capture_line` | `os.apps.sshd.ssh_session_helpers` |
| `test/integration/os/apps/sshd/.spipe_wrapped_entry_ssh_aes256_gcm_packet_spec.spl` (L4) | 1 | `ssh_aes256_gcm_replay_capture_line` | `os.apps.sshd.ssh_session_helpers` |
| `test/integration/rendering/simd_parity_spec.spl` (L31) | 1 | `simd_rendering_manifest_entry` | `compiler.mir_opt.optimizer_manifest` |
| `test/integration/rendering/engine2d_font_owner_native_probe.spl` (L1) | 1 | `engine2d_font_owner_current` | `std.gc_async_mut.gpu.engine2d.font_owner` |
| `test/integration/rendering/screenshot_compare_helpers.spl` (L6) | 1 | `BackendCompareEntry` | `os.compositor.screenshot_compare` |
| `test/03_system/game2d_archtest_spec.spl` (L25) | 1 | `repeat_str` | `std.common.text` |
| `test/03_system/simpleos_desktop_with_apps_framebuffer_spec.spl` (L25) | 1 | `send_harness_marker` | `os.compositor.qemu_capture` |
| `test/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.spl` (L25) | 1 | `send_harness_marker` | `os.compositor.qemu_capture` |
| `test/fixtures/concurrency_api_misuse/numbered_thread_spawn_alias_import.spl` (L1) | 1 | `thread_spawn2` | `std.concurrent.thread` |
| `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl` (L25) | 1 | `send_harness_marker` | `os.compositor.qemu_capture` |

### B.3 DEAD-AND-HARMLESS — 42 entries across 29 specs

| spec (canonical) | n | undeclared names | modules |
|---|---|---|---|
| `test/feature/app/t32_tools/t32_mcp_bugfix_spec.spl` (L26) | 5 | `t32_LB`, `t32_RB`, `t32_extract_field`, `t32_jp`, `t32_js` | `app.mcp_t32.json_helpers` |
| `test/feature/app/t32_tools/t32_lsp_mcp_spec.spl` (L22) | 4 | `lsp_LB`, `lsp_Q`, `lsp_RB`, `lsp_jo2` | `app.t32_lsp_mcp.json_helpers` |
| `test/unit/app/t32_cli/error_codes_spec.spl` (L3) | 2 | `T4010`, `T4040` | `app.t32_cli.error_codes` |
| `test/unit/app/t32_cli/error_messages_spec.spl` (L3) | 2 | `cli_commands`, `cli_shell_commands` | `app.t32_cli.error_codes` |
| `test/unit/lib/debug/remote/t32_ffi/t32_types_spec.spl` (L3) | 2 | `T32_ERR_APILOCK_FAIL`, `T32_ERR_EXECUTECOMMAND_FAIL` | `std.debug.remote.t32_ffi.t32_types` |
| `test/integration/rendering/screenshot_compare_helpers.spl` (L6) | 2 | `compare_with_tolerance`, `print_multi_backend_report` | `os.compositor.screenshot_compare` |
| `test/feature/app/t32_tools/t32_mcp_spec.spl` (L20) | 2 | `t32_SB_L`, `t32_SB_R` | `app.mcp_t32.json_helpers` |
| `test/integration/rendering/backend_screenshot_compare_spec.spl` (L11) | 2 | `capture_software`, `compare_with_tolerance` | `os.compositor.screenshot_compare`, `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture` |
| `test/unit/browser_engine/anonymous_block_spec.spl` (L6) | 1 | `be_dom_get_tag_name` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| `test/unit/browser_engine_standalone/anonymous_block_spec.spl` (L6) | 1 | `be_dom_get_tag_name` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| `test/unit/lib/blink/css_selector_spec.spl` (L23) | 1 | `dom_tree_new` | `std.blink.dom.node` |
| `test/unit/lib/common/proton_real_exec_spec.spl` (L3) | 1 | `proton_non_wine_runtime_evidence_new` | `common.proton_runtime_subsystems` |
| `test/unit/lib/crypto/chacha20_spec.spl` (L13) | 1 | `chacha20_keystream` | `std.crypto.chacha20` |
| `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl` (L41) | 1 | `Core64StepResult` | `std.hardware.rv64gc_rtl.core` |
| `test/unit/lib/hardware/rv64gc_rtl/.spipe_wrapped_entry_core64_integration_spec.spl` (L2) | 1 | `Core64StepResult` | `std.hardware.rv64gc_rtl.core` |
| `test/unit/lib/http_server/csrf_spec.spl` (L12) | 1 | `default_csrf_config` | `std.http_server.csrf` |
| `test/unit/lib_standalone/blink/css_selector_spec.spl` (L23) | 1 | `dom_tree_new` | `std.blink.dom.node` |
| `test/unit/lib_standalone/common/proton_real_exec_spec.spl` (L3) | 1 | `proton_non_wine_runtime_evidence_new` | `common.proton_runtime_subsystems` |
| `test/unit/os/__tmp_adapter_probe_spec.spl` (L3) | 1 | `_device_mapping` | `os.kernel.memory.memory_leveling_device_adapters` |
| `test/integration/rendering/glass_pipeline_screenshot_spec.spl` (L11) | 1 | `compare_with_tolerance` | `os.compositor.screenshot_compare` |
| `test/03_system/simpleos_desktop_framebuffer_spec.spl` (L75) | 1 | `send_harness_marker` | `os.compositor.qemu_capture` |
| `test/feature/app/t32_tools/t32_mcp_tools_spec.spl` (L23) | 1 | `t32_parse_catalog_entry` | `app.mcp_t32.window_tools` |
| `test/feature/web_platform/css/wpt_scorecard_spec.spl` (L14) | 1 | `interpolate_keyframes` | `std.gc_async_mut.gpu.browser_engine.style.animation` |
| `test/03_system/os/simpleos_desktop_framebuffer_spec.spl` (L75) | 1 | `send_harness_marker` | `os.compositor.qemu_capture` |
| `test/feature/web_platform/css/animations_wpt_spec.spl` (L3) | 1 | `interpolate_keyframes` | `std.gc_async_mut.gpu.browser_engine.style.animation` |
| `test/fixtures/concurrency_api_misuse/spawn_isolated_number_suffix_alias.spl` (L1) | 1 | `spawn_isolated2` | `std.concurrent.thread` |
| `test/fixtures/concurrency_api_misuse/spawn_limited_number_suffix_alias.spl` (L1) | 1 | `spawn_limited2` | `std.concurrent.thread` |
| `test/fixtures/concurrency_api_misuse/thread_spawn_number_suffix_alias.spl` (L1) | 1 | `thread_spawn2` | `std.concurrent.thread` |
| `test/system/simpleos_desktop_framebuffer_spec.spl` (L75) | 1 | `send_harness_marker` | `os.compositor.qemu_capture` |

## 2026-08-10 — this FIXED status was only HALF TRUE until now

`test/01_unit` and `test/unit` (and `test/02_integration`/`test/integration`)
are duplicate trees and **both execute** — `test_runner_new` has no path
allowlist. The fix recorded above landed on only ONE leg of
`os/compositor/wm_action_applier_spec.spl and lib/common/window_protocol/input_translator_spec.spl`. For \`input_translator_spec\` the divergence was pure block order; for \`wm_action_applier_spec\` the two legs had each received a DIFFERENT repair, so that one needed a genuine merge — and the merged spec is RED for an unrelated, pre-existing reason filed as \`wm_action_applier_spec_dead_on_both_legs_vulkan_order_env_get_2026-08-10.md\`.
So this document read FIXED while the defect was still live on a tree that
runs on every `bin/simple test`.

Completed 2026-08-10 in commit `f6a6145ad4d5002731d019f3b0cc13b19c4c8b54 / b5119f4889e5fa2226451f845f53b55b80f5029e`, which converges the pair and trims
`scripts/check/test_tree_divergence_baseline.txt` accordingly. Census and
method: `doc/08_tracking/test/half_landed_fixes_across_duplicate_test_trees_2026-08-10.md`.
The class is now fenced: `scripts/check/check-test-tree-divergence.shs`
fails a push whose range edits one leg and leaves the twin divergent.
