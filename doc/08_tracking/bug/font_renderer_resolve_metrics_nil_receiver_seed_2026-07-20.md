# font_renderer: resolve_font_metrics_with_language nil-receiver crash under seed (blocks WM Draw IR composition + widget_draw_ir)

**Status:** STILL OPEN 2026-07-21 — two root-fix lanes deep. **Do not read
this as fixed.**

- Lane 1 (`/tmp/wt_ttfcrash`): root-caused+mitigated a mutex nil-unwrap bug on
  the `run`-path only — see "Mutex bug (run-path, mitigated)" below. Proved
  that's NOT what blocks the actual `bin/simple test` spec.
- Lane 2 (`/tmp/wt_fontvalidate`, this update): root-caused the REAL
  `bin/simple test` blocker down to `sha256_u8_hex`'s compression-round loop
  crashing under the Rust seed interpreter at a call-stack-depth-dependent
  iteration count — a seed interpreter defect, not a font_registry.spl bug.
  See "Root cause found (2026-07-20/21, second root-fix lane)" below for full
  evidence, blast radius (also hits `font_asset_manifest_spec.spl`), and what
  was and wasn't fixed. No safe .spl-level root fix identified; two new
  passing regression tests added for the missing/malformed-input error path
  that doesn't depend on the buggy loop.

- A real, root-caused bug in `_font_mutex_acquire`/`_font_mutex_release`
  (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`) is confirmed and
  its hard crash is mitigated **on the `bin/simple run` evaluator only** — see
  "Mutex bug (run-path, mitigated)" below.
- **This is NOT what blocks `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
  under the actual `bin/simple test` command**, which is the deliverable this
  bug doc is about. Probe evidence (below, "Actual bin/simple test blocker")
  shows the real spec crashes earlier and elsewhere: inside
  `validate_selected_font_asset` (`src/lib/common/encoding/font_registry.spl:514`),
  called from `FontRasterizer._load_selected_bytes`
  (`src/lib/nogc_sync_mut/sffi/spl_fonts.spl:176`), reached from
  `FontRenderer.try_load_selected_bytes` — well before any mutex code runs.
  `font_renderer_spec` still fails with `Passed: 0 / Failed: 1` after this
  pass's changes, identical in shape to before.
- Project note for future readers of this doc: `simple test` (SSpec) uses a
  **different evaluator** than `simple run`. A fix verified only via `run`
  does not establish anything about the `test` path. This doc originally (and
  wrongly, for one intermediate revision) claimed "FIXED" based on `run`-only
  evidence; corrected here after adding evaluator-matched probes.

## Mutex bug (run-path, mitigated)

Confirmed via minimal isolated repros (no font code) and gdb: the shared
mutex-facade helpers `_font_mutex_acquire`/`_font_mutex_release` (top of
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`), used by every lock in
this file (`_resolved_font_metric_lock`, `_browser_default_font_lock`,
`_font_atlas_dependency_generation_lock`), used to unwrap their `Mutex?`
parameter with `current ?? mutex_new(0)` into a single `val`. Under the Rust
seed's `run` evaluator, when the module-level `Mutex?` var's Some-payload came
from the declaration's own `mutex_new(0)` initializer (module-init time), the
`??` operator produced a value that reports `== nil` as `false` but crashes as
"field access on nil receiver" the instant a method (`.lock()`) is called on
it. A local-var-initialized `Mutex?` source unwraps fine via `??`; the
identical module-var-initialized source faulted every time, reproduced via
`bin/simple run` on a standalone script (`FontRenderer.new()` + real TTF load
+ `prepare_text("A"/"", ...)`, which exercises
`_activate_render_config -> _reset_font_atlas ->
_next_font_atlas_dependency_generation -> _font_mutex_acquire`).

Applied mitigation: the three lock module vars now initialize to `nil` at
declaration (matching the file's own already-documented
freestanding/native-build lazy-init intent) and
`_font_mutex_acquire`/`_font_mutex_release` unwrap via a guard clause + `.?`
instead of `??`. This converts the **hard SIGILL crash into a silent
no-op**: gdb + probe evidence on the `run` path shows `.?` still yields a
value that dynamically dispatches as `bool` in this context ("Runtime error:
Function 'bool.lock'/'bool.unlock' not found", non-fatal, execution
continues) — the mutex still does not actually lock/unlock. This is real
value-corruption in the Rust seed's `Mutex?` handling that this pass did NOT
fully root-cause; it only stopped the fatal half. See the "not fully closed"
framing above -- do not treat the `.?`/nil-init change as more than a
crash-to-noop mitigation on a path that, per the next section, is not even
what the actual spec exercises.

## Actual `bin/simple test` blocker (probe-localized, 2026-07-20)

Adding `print()` probes directly in the real spec file and in
`_load_selected_bytes` (temporarily, for diagnosis, not committed) and
running the real `bin/simple test test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
localized the actual crash precisely:

```
✓ rejects nil or stale rasterizers through is_current
SPECPROBE:it-entered
SPECPROBE:path-set
SPECPROBE:renderer-constructed
SPECPROBE:bytes-read len=1708408
PROBE:lsb-enter blob_len=1708408
PROBE:lsb-post-identity id_len=94
PROBE:lsb-pre-validate
<process dies here -- no further probe output, no "renders a selected
face..." example ever runs, Test Summary: Passed 0 / Failed 1, Duration ~67s>
```

So under `bin/simple test`, `FontRenderer.new()`, `file_read_bytes(path)`, and
entry into `_load_selected_bytes` all succeed; the process dies during
`validate_selected_font_asset(ttf_path, blob)`
(`src/lib/common/encoding/font_registry.spl:514`, called from
`FontRasterizer._load_selected_bytes` at
`src/lib/nogc_sync_mut/sffi/spl_fonts.spl:188`). That function does real
1.7MB-blob work (`sha256_u8_hex`, `validate_glyf_font_instance`,
`sfnt_manifest_tables_match`, `sfnt_manifest_names_match`) with no obviously
unsafe .spl statement visible at the call-site level probed. This is
upstream of and unrelated to the mutex code above -- it never gets called
under the `test` evaluator's crash path. Not investigated further in this
pass per scope (avoiding an open-ended native/SFFI-adjacent rabbit hole after
one bounded probe cycle, per the mission's own timeboxing guidance) -- the
next step for whoever picks this up is to probe inside
`validate_selected_font_asset`/`validate_glyf_font_instance` specifically
under `bin/simple test` (not `run` -- the two evaluators disagree here; `run`
reaches `try_load_selected_bytes = true` successfully on the same file, so
this is `test`-evaluator-specific and must be diagnosed on that evaluator).

## Root cause found (2026-07-20/21, second root-fix lane, worktree `/tmp/wt_fontvalidate`, pinned base `26a5e7394074836c2e2741d4b97f0a1ebb6ddd82`)

**This is a Rust-seed interpreter defect, not a font_registry.spl bug.** Localized
by probe-instrumenting (temporarily, all removed and grep-verified clean
before this commit) `_validate_selected_font_asset`
(`src/lib/common/encoding/font_registry.spl:490`) and
`sha256_u8_hex` (`src/lib/common/crypto/sha256.spl:184`):

1. The crash is inside `sha256_u8_hex(blob)`, called from
   `_validate_selected_font_asset` at what was line 505 before probes were
   removed (now line ~499, `val actual_sha256 = sha256_u8_hex(blob)`). Every
   step before that call (`env_get`, `selected_font_asset_candidates()`,
   candidate lookup, byte-length compare) completes and prints; the crash is
   always inside the SHA-256 computation itself, never in font_registry's own
   validation logic.
2. `sha256_u8_hex` is **logically correct** on this exact 1.7MB blob: a
   minimal standalone `fn main()` script (no `describe`/`it`, no
   font_registry) that reads
   `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
   and calls `sha256_u8_hex` on it completes successfully and prints the
   correct hash `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`
   (matches the value hardcoded in `font_renderer_spec.spl`'s
   `to_start_with("sha256=2cb2adb378a8f574")` assertion), both with and
   without `SIMPLE_RUNTIME_MODE=interpreter` set (the env var the test-runner
   child sets). No crash, no wrong output — twice, deterministically.
3. Progress-probing `sha256_u8_hex`'s block loop (print every 2000 of 26695
   total 64-byte blocks) shows the crash point is **call-stack-depth
   dependent**, not data-dependent or iteration-count-dependent in isolation:
   - Called from `_validate_selected_font_asset` (deepest probed context):
     dies at block_offset ≈544000 (~8500 blocks).
   - Called directly from a minimal `describe`/`it` wrapper (shallower, no
     font_registry layers): dies at block_offset ≈672000 (~10500 blocks).
   - Called from bare `fn main()` (shallowest): completes all 26695 blocks,
     no crash, correct hash — twice.
   Removing base call depth reliably buys more survivable loop iterations;
   adding it costs iterations. This pattern (not the data, not the total
   iteration count alone) is the signature of a native/interpreter resource
   budget consumed per something-inside-the-loop, compounding with
   pre-existing call depth.
4. **Bisected within `sha256_u8_hex` itself**: temporarily disabling only the
   final compression-round loop (`while ri < 64: ... k[ri] ... w[ri] ...
   rotr32(...) ...`, an 8-variable rotation with 2 XOR/AND-heavy expressions
   and two different-array reads per iteration) while leaving the two
   message-schedule loops (fast-path byte read + `wi=16..64` expansion, which
   also use `rotr32`, XOR, array read/write, and `& mask32`) fully intact and
   unchanged: the function then runs to completion for **all 26695 blocks**
   with no crash (verified via the `describe`/`it` wrapper that previously
   died at block ≈672000). The crash is specifically inside the compression
   round loop's shape, not the message-schedule loops, not `rotr32` alone,
   not array indexing alone.
5. Seven targeted synthetic probes under the SAME `describe`/`it` seed
   `bin/simple test` context — each isolating ONE structural feature of the
   real compression loop at 30000 iterations (well above the ~8500-10500
   block crash point) — **all passed with no crash**: a bare
   accumulator loop; a loop with 8 `val` bindings/iteration; triple-nested
   loops (matching the 16+48+64 inner-loop shape) with simple vals; a loop
   calling a `rotr32`-shaped helper function ~5 times/iteration (480
   calls/outer-iteration, matching the real loop's call density); a loop
   doing index-assignment + index-read on a reused small array (matching
   `w[wi]=...`); large-array (the real 1.7MB blob) indexed reads across the
   full offset range; and an 8-variable rotation loop shaped exactly like the
   compression round's `a..hh` rotation. None reproduced the crash in
   isolation — only the REAL compression loop's specific combination
   (rotr32 + XOR + AND + two-array reads + 8-var rotation + `& mask32`
   truncation, all together) triggers it. This was not pinned to one root
   Rust source line within the time-boxed budget for this lane; going further
   means instrumenting `src/compiler_rust/compiler/src/interpreter*` directly,
   which is out of scope here (seed is bootstrap-only, a sibling lane owns the
   bootstrap/build cache this session, and repo policy is fix-.spl-first).
6. **Blast radius is bigger than `font_renderer_spec.spl`**: the same crash
   (identical signature: dies silently, `error: test-runner: no examples
   executed`/`spec failed`, ~64-77s, no signal message captured on merged
   stdout+stderr) also reproduces on
   `test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl`, which
   loops `load_selected_font_file` over all 16 selected font candidates
   (including the same large Noto Sans Mono asset). Its own `it`-local
   coverage for missing/byte-length paths (lines 10, 37) is real and correct
   but currently unreachable because the crash happens earlier in the same
   `it` block's candidate loop.
7. **Not verified against the self-hosted pure-Simple `bin/simple`** this
   session — only the Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`,
   prints the "bootstrap seed only" warning on every invocation) was
   available; a sibling lane owned the bootstrap build this session. Re-run
   `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` and
   `font_asset_manifest_spec.spl` against the self-hosted binary once
   available — if the self-hosted binary does NOT reproduce this, it is a
   legacy seed-only defect (still worth fixing since the seed remains the
   bootstrap path, but lower priority); if it DOES reproduce, this needs a
   fix in the pure-Simple compiler/interpreter, not the Rust seed.

### Fix applied this lane

`sha256_u8_hex`/`_validate_selected_font_asset` were left **unchanged**
(reverted back to identical-to-base after the bisection probes above — `git
diff` on both files is empty). No safe, root-cause fix was identified within
this lane's budget; hoisting/restructuring the compression loop's locals was
not attempted live since the isolation probes (item 5) already show simpler
restructurings of the same shape do NOT reproduce the crash, so a
speculative restructuring risks silently changing behavior without any way
to prove it dodges the real bug's exact trigger.

What WAS fixed: `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
gained two new fast, real regression cases (both currently pass, `✓` printed)
proving that a missing or malformed selected-font input already produces a
clean `false`/error return through `_validate_selected_font_asset`'s
byte-length short-circuit — **before** the crash-prone `sha256_u8_hex` path
is ever reached — never a crash:

- `"rejects a truncated selected-asset blob with a clean failure, not a
  crash"` — a 16-byte slice of the real NotoSansMono blob on its own managed
  path fails the byte-length check and `try_load_selected_bytes` returns
  `false`.
- `"rejects an unmanaged/missing font path with a clean failure, not a
  crash"` — an unknown path with an empty blob returns `false` via the
  `cand_identity == ""` unmanaged gate.

These exercise the exact "if a font fails to load, produce a real error
callers handle, not a nil that crashes later" requirement for the paths that
don't require hashing the full asset. The third pre-existing `it` ("renders a
selected face from owned bytes...") still crashes the process for the
already-root-caused reason above; it is left red/undisguised, not skipped.

### Spec before/after (seed, `bin/simple test`, this lane)

Before (baseline, matches prior lane's finding): `font_renderer_spec.spl` —
first example passes (`✓ rejects nil or stale rasterizers...`), process dies
during the second example, `Test Summary: Passed 0 / Failed 1`, ~67-70s,
`error: test-runner: spec failed`.

After (this lane's two new examples added, `sha256`/`font_registry` back to
base): same file now prints THREE real passes before the crash —
`✓ rejects nil or stale rasterizers through is_current`,
`✓ rejects a truncated selected-asset blob with a clean failure, not a
crash`, `✓ rejects an unmanaged/missing font path with a clean failure, not a
crash` — then still dies on `"renders a selected face..."` for the
root-caused reason above. `Test Summary: Files 1, Passed 0, Failed 1,
Duration ~64.7s` (the test-runner's own aggregation does not currently credit
real passes recorded before a process-level crash — a separate, pre-existing
test-runner reporting gap, not addressed here).

## Old text below is the original 2026-07-20 filing, kept for history.**

**Status:** OPEN 2026-07-20 — found while adding WM close-lifecycle specs (G2 lane).
**Severity:** Blocking for seed-run WM/GUI specs — `shared_wm_scene_draw_ir_composition` cannot execute at all under the Rust seed; origin/main's own `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` currently aborts at its second example (1 pass printed, then process death, Test Summary `Passed: 0 / Failed: 1`).
**Affected file:** `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (`resolve_font_metrics_with_language`, line ~1635)
**Blast radius:** `src/lib/common/ui/window_scene_draw_ir.spl` (`_wm_draw_ir_text` -> composition), `src/lib/common/ui/widget_draw_ir.spl` (`_default_text*` -> `widget_tree_to_draw_ir`)
**Path:** `bug` track.

## Symptom

Minimal repro (seed `bin/simple run`, repo root, verified at origin/main 6aa78042c14
with a pristine tree):

```
use std.common.encoding.font_registry.{simpleos_default_font_asset_candidate}
use std.nogc_sync_mut.text_layout.font_renderer.{resolve_font_metrics_with_language}

fn main():
    val candidate = simpleos_default_font_asset_candidate()   # ok: "Noto Sans Mono"
    val m = resolve_font_metrics_with_language(candidate.family, "T", 12, "und")
    # -> "runtime error: field access on nil receiver", then SIGILL core dump
```

`simpleos_default_font_asset_candidate()` itself succeeds. The crash is inside
the resolve path (first suspect: `_resolve_font_metrics_with_language_config`
dereferencing a nil registry/glyph record).

## Blast radius (all verified individually)

1. `shared_wm_scene_draw_ir_composition(scene, taskbar, ...)` crashes for ANY
   scene — even borderless-only windows with an empty taskbar and empty clock
   label (the chrome batch also emits text). Bisect: `_wm_draw_ir_desktop_batch`
   fine; `_wm_draw_ir_window_batch` dies in `_wm_draw_ir_text`; a direct
   `_wm_draw_ir_text("t", 66, 19, 0, 28, "T", color, "und")` call dies the same
   way; `wm_chrome_theme()` and `_wm_draw_ir_window_box` are fine.
2. `widget_tree_to_draw_ir_cpu` dies identically even for RECT-ONLY trees
   (button with empty label + progress bar); `common.ui.builder` +
   `compute_layout` alone are fine.
3. On the SSpec test path the crash surfaces as `error: test-runner: no
   examples executed` when the first example touches composition, or as an
   abort mid-file after earlier examples pass (the current
   `window_scene_draw_ir_spec` shape).

Note: `window_scene_draw_ir_spec`'s FIRST example ("retains readable bitmap
text when selected metrics are unavailable") passes, so the invalid-metrics
fallback path works; the crash is on the metrics-resolution path that runs when
a real font candidate is found.

## Not caused by

- The 2026-07-20 WM close-lifecycle changes (G2): reproduced on a pristine
  origin/main tree; no `src/lib`/`src/runtime` file changed in
  93abfa3c6b2..6aa78042c14, so the breakage predates that range's tip motion.

## Blocked tests (explicit skips, not silently dropped)

- `test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl`
  records three skips (composition card census with close/traffic nodes,
  stale-node sweep after close recompose, drawn-rect vs dispatch lockstep) and
  a NOTE for the widget_draw_ir composition specs. Un-skip and implement when
  this bug lands.
