# Array-loss / Dict.get-Option compiler-fix campaign — execution runbook

Status: **ready to execute, blocked only on a bootstrap window.** Nothing here
is applied yet. This runbook exists so the campaign can start the instant a
window opens, without re-deriving scope or gates.

Primary source: `doc/08_tracking/bug/cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`
(bug doc). Draft diffs + reports live in the session scratchpad (not yet
committed — see §1 for exact paths).

---

## 1. Scope

Two independent draft diffs, three fixes, all still uncommitted:

### 1a. `compiler_array_loss_fix.diff` (scratchpad) — fixes A1 + B2 only

Touches `src/compiler/50.mir/_MirLowering/module_lowering.spl`,
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
`src/compiler/50.mir/mir_lowering_types.spl` (3 files, 122 insertions / 3
deletions). Report: `freestanding_array_loss_rca.md`.

- **A1 — nested-array element identity.** `expr_dispatch.spl`'s indexed-element
  read only registered `runtime_array_locals` when the element was a *named
  struct*; an element that is itself an array (`[[text]]`, `[[i64]]`) fell
  through undetected, so `nested[i].len()` / `nested[i][j]` decoded the handle
  as a scalar and read empty. Fix adds the array-analogue of the struct-name
  registration, gated on the existing `"__runtime_array__"` sentinel, mirroring
  `emit_resolved_direct_call`'s existing Array/Slice return handling.
- **B2 — loud diagnostic for mutated array globals.** `952d2ca34d7`'s
  re-lowering fallback (re-run the original initializer at every read instead
  of real storage) is sound only for a never-mutated `val`; a mutated
  array-typed global silently drops every write (`module=0` in the RCA). B2
  restores noise: `report_mutable_array_global` prints
  `[mir-lower] WARNING: mutable array-typed module global '<name>' has no
  backing static: ...` once per symbol, promotable to a hard lowering error via
  `SIMPLE_STRICT_ARRAY_GLOBALS=1`. **This is a diagnostic only — it does not
  give the global real storage.**
- **Deliberately NOT in this diff:** Fix B1 (real null-init `MirStatic` slots +
  cranelift `__module_init_*` wiring — the actual storage fix for array
  globals) and Fix A2 (gate the `SIMPLE_BOOTSTRAP=1` text-coercion default that
  amplifies the loss in the freestanding/guest lane). The RCA's own suggested
  order is **A1 → B2 → B1 → A2**; only the first two are drafted. Do not treat
  this campaign as closing the array-loss bug — it converts silent corruption
  into a loud, still-broken-but-honest failure for globals, and fixes one
  concrete nested-array read pattern.

### 1b. `dict_get_option_fix.diff` (scratchpad) — Dict.get / Option match-decoder fix

Touches `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
(native MIR lane), `src/compiler/10.frontend/core/interpreter/eval.spl` +
`eval_tables.spl` (tree-interpreter lane), plus a new spec
`test/01_unit/language/dict_get_option_match_spec.spl` (4 files, 353
insertions / 1 deletion, 15 examples). Report: `dict_get_option_fix_report.md`.

- **Decision: fix the decoder, not the producer.** Option has a deliberate
  dual physical ABI in this codebase (BOXED via `rt_enum_new`, FLAT raw-or-nil
  i64 word) — `?`, `??`, `.unwrap()`, and `if val Some(x) = …` already
  discriminate both lanes at runtime. **Only `match … case Some(x)` was never
  taught the flat lane**, so a match on `Dict.get(k)`'s result always took the
  `Some` arm with a nil/garbage payload (or, on native, fell to the default
  arm). Native lane: `lower_enum_match` gets a flat/boxed lane discriminator
  (`rt_enum_discriminant(scrut) != -1` selects boxed) and the payload reader
  switches to `rt_unwrap_or_self` (dual-lane already in the runtime). Tree
  interpreter: `match_pattern` gets its first real enum-variant cases (`None`
  as a nullary pattern, `EXPR_CALL`/`EXPR_FIELD_ACCESS` variant patterns) — it
  previously had **no enum case at all** and fell to an equality default that
  both left `hit` unbound and made a bare `case None:` bind-and-match
  *everything*.
- **Blast radius, measured (from the report):** total `.get(` calls in owned
  `.spl` = 11,815 across 1,881 files. Breakdown by consumer pattern:

  | pattern | occurrences |
  |---|---|
  | `x.get(k) ?? default` | 864 |
  | `if val … = x.get(k)` | 166 |
  | `match x.get(k)` | **507** (257 confirmed `case Some/None`) |
  | nil-tested (`.?` 993, `==`/`!=` nil 91, `== Some/None` 95, `?.` 4) | 1,183 |
  | `?`/`!` unwrap | 307 |
  | raw/direct use (remainder) | ~8,788 |

  The rejected alternative (wrap `Dict.get` itself in boxed Some/None) would
  touch an estimated 4,000-4,600 Dict-only call sites, ~2,500-3,000 of which
  consume the value raw today and would silently start receiving an enum
  handle (plus break `== nil` on every miss). The chosen fix (teach the
  decoder) touches only the ~507 `match … .get()` sites, **all of which are
  broken today** — nothing that currently works changes behavior.
- **Rust seed:** NOT patched (`.claude/rules/*` "Fix .spl not Rust" /
  "Pure Simple First" rule). A seed-side mirror patch is documented in the
  report §5 for the record only; do not apply it as part of this campaign.
- **Nothing in this diff was executed** — no self-hosted `run`/`test` lane
  existed in the drafting checkout (deployed `bin/simple` is the Rust seed;
  `build/bootstrap/stage3/.../simple` has no `run`/`test` subcommand). The
  `.spl` changes are review-verified only. This campaign's entire job is to
  actually run them for the first time.

### Explicitly out of scope for this campaign

Everything else the bug doc catalogs as already-landed workaround commits
(font tuple-return fix, `FontRasterizer.invalid()` sentinel, chained
`.to_i32()`/erased-receiver dispatch fixes, `interp_env_get_name_collision`)
is a **different defect class** and is not touched by either diff. See §5 for
which of those become un-conversion candidates once this campaign lands.

---

## 2. Preconditions

- **No lanes running.** Check for concurrent `native-build`/`bootstrap`/`test`
  processes before starting (`ps aux | grep -E 'simple (native-build|test)|bootstrap-from-scratch'`)
  and check other agent worktrees under `.claude/worktrees/agent-*` for
  in-flight work. `.claude/worktrees/lane-runner` in particular already has
  uncommitted state (a staged `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-26.md`
  and a modified `tools/tauri-shell/.../gradlew.bat`) — either coordinate with
  whatever session owns it or use a **separate, freshly-created worktree** for
  this campaign so its diffs don't land on top of unrelated uncommitted files.
- **Memory headroom — do not trust the "~18GB with interning" number at face
  value.** The MEMORY.md one-line summary of
  `reference_stage4_bootstrap_killed_by_resource_monitor_64gb_cap.md` says
  "stage4 peaks ~65GB (unfixed) / ~18GB (interning-fixed)", but the full
  memory doc's own **most recent, controlled** measurement (2026-07-25, two
  runs differing only in interning, landing within 0.5% of each other)
  concluded the opposite: **stage4 full-CLI peaks ~111GB regardless of
  seed-interning, backend, or mode**, and both runs were killed by `earlyoom`
  (SIGTERM, no binary produced). The ~65GB figure is the **kill point** of
  `scripts/resource/kill_simple_monitor.shs`'s generic RSS cap
  (`KILL_ANY_MEM_MB=64000` default), not the true peak — the monitor was
  simply truncating observation before the real ~111GB peak was ever reached.
  Flagging this explicitly per the "consult history before arch claims" rule:
  **plan for ~111GB+ headroom, not ~18GB.** Concretely, before starting stage4:
  - Confirm available RAM on the build box (`free -g`) covers ~112GB+, or
  - Raise the monitor cap for this run only: `KILL_ANY_MEM_MB=120000 sh
    scripts/resource/kill_simple_monitor.shs` (does not affect an
    already-running monitor instance — must be set before the monitor starts),
    or
  - Use the repo's own local unblock (bootstrap script already copies the
    stage4 binary to a scratch name; the documented workaround is to make that
    copy's argv[0] contain `claude` so `is_protected()` skips it) **only** as a
    last resort, and record a bug when doing so — this is explicitly flagged
    as a local-only, do-not-commit workaround, not a fix.
  - This campaign's diffs are unrelated to the actual stage4 memory driver
    (`evict_*` reassigns containers but never frees — a separate, still-open
    defect), so stage4 will hit the same ~111GB regardless of these fixes
    landing cleanly. Do not interpret a stage4 monitor-kill as a regression
    from this campaign's changes.
- **Disk.** No hard quota is documented. Each `build/bootstrap/stage{2,3,4}/<triple>`
  tree plus native-cache plus the WM evidence artifact directories
  (`build/wm-production-fullscreen-evidence/`,
  `build/simpleos-wm-fullscreen-evidence/` or similar `check-*.shs`
  `$BUILD_DIR`s) can each run multi-GB. Check `df -h` headroom before starting,
  and budget for repeated `rm -rf $BUILD_DIR/native-cache` (mandatory between
  bisection/smoke cycles — see §3d).
- **Binaries/seeds that must exist:**
  - `src/compiler_rust/target/bootstrap/simple` — the Rust seed. Bootstrap-only;
    must exist for Stage 2 to run at all.
  - The currently **deployed** `bin/release/<triple>/simple` is, per the
    2026-07-25/26 showcase-matrix evidence, still a **Rust bootstrap seed**
    build in some collected evidence, not the pure-Simple self-hosted binary —
    verify which one is actually live before assuming `bin/simple` exercises
    the `.spl` compiler. `check-wm-production-fullscreen-evidence.shs` and
    `check-simpleos-wm-fullscreen-evidence.shs` both resolve the first
    non-seed binary among `build/bootstrap/stage3/*/simple`,
    `stage2/*/simple`, `bin/release/*/simple` themselves — trust their
    resolution logic, not an assumption about `bin/simple`.
  - `build/bootstrap/stage3/<triple>/simple` (produced by this campaign's own
    bootstrap run) is **compile-only** — `simple-bootstrap 1.0.0-beta`, usage
    `simple compile <file> …`, **no `run`, no `test` subcommand**. Do not
    expect to `run`/`test` directly against it; it is a codegen surface for
    the `native-build`-based `check-*.shs` harnesses only.

---

## 3. Exact sequence

### 3a. Apply diffs in a dedicated worktree

1. Create a fresh worktree off current `main` tip (do **not** reuse
   `.claude/worktrees/lane-runner` — see §2). Follow the repo's existing
   `.claude/worktrees/agent-*` naming convention.
2. Both diffs are file-disjoint (`compiler_array_loss_fix.diff` touches
   `module_lowering.spl` / `expr_dispatch.spl` / `mir_lowering_types.spl`;
   `dict_get_option_fix.diff` touches `switch_operators_calls.spl` /
   `eval.spl` / `eval_tables.spl` / the new spec) — order of application does
   not matter. `git apply --check` each, then apply both, then commit once per
   diff (two commits keeps §4's per-fix revert clean).
3. Confirm with `git status`/`jj status` that nothing beyond the diffs'
   declared files changed.

### 3b. Build order

Per `.claude/rules/bootstrap.md`: this is a **T3 — full bootstrap** change
(the compiler itself changed, `src/compiler/50.mir/**` and
`src/compiler/10.frontend/core/interpreter/**`), which subsumes T1/T2.

1. **Stage 2** — seed native-builds `bootstrap_main.spl` with `SIMPLE_BOOTSTRAP=1`
   exported globally (this is what the bootstrap wrapper does by default; note
   it forces the real-LLVM bootstrap emit path for a narrow entry-closure, a
   different shape than the full driver — this is expected, not a defect).
2. **Stage 3** — stage2 recompiles the changed `.spl` via `${backend}` (this
   is the step that actually proves the seed *can* build the new pure-Simple
   source; if it fails, the new source needs a Rust-seed feature that doesn't
   exist and needs `--full-bootstrap`, not a source workaround). **Stage 3 has
   no `run`/`test` subcommand** (§2) — it is a codegen artifact consumed by the
   `check-*.shs` harnesses, not something to invoke directly.
3. **Stage 4** — the full-CLI self-host build. This is the memory-heavy stage;
   see §2's headroom note before starting it.
4. Run via `bin/simple build bootstrap` — per `.claude/rules/commands.md` this
   is exactly the **3-stage self-compilation verification**. Use
   `--full-bootstrap` only if Stage 2/3 report the seed cannot build the
   changed source.

### 3c. Extended smoke matrix

Run in this order — cheapest/most targeted first, escalating to full-scale WM
evidence:

1. **`probes/cranelift_aggregate_return_min.spl` — the minimal repro.**
   - Interpreted (`run`): expect `AGG_MIN_PASS`. Pre-fix, probe 3
     (`Dict.get` + `match Some` + field access) crashes
     `runtime error: field access on nil receiver` on both the seed and the
     self-hosted interpreter; probes 1/2/4 already pass. Post-fix, all four
     probes (including 3) must print `AGG_MIN_PASS`, rc=0.
   - Native (`native-build --backend cranelift --mode dynload --entry-closure
     --strip` then execute): same expectation. Probes 1/2/4 already passed at
     this minimal scale pre-fix per the bug doc — probe 3 crossing to PASS is
     the actual delta this smoke step verifies.
2. **`test/01_unit/language/dict_get_option_match_spec.spl` under `test`.**
   Expect all **15 examples green**: Dict.get+match Some/None (struct/text/i64
   payload, hit and miss), raw-or-nil consumers unchanged (`??`, `==`/`!=`
   nil, `if val`, `get_or`), boxed-enum matching unaffected (nullary variant,
   catch-all binding, boxed `Result` `Ok(v)`). Pay particular attention to the
   **text-payload case** (probe/spec case 2) — the report flags it as "the
   single most likest post-bootstrap failure" because the native lane's
   single-field payload path may not re-type a flat text handle correctly.
3. **Regression control:** `test/01_unit/language/array_repeat_spec.spl` — a
   pre-existing known-good spec, unrelated to this fix, used as a harness
   sanity control in the report. It must also execute cleanly under the
   now-fixed self-hosted `test` runner (under the seed it reported "no
   examples executed" for both this and the new spec — a seed harness
   limitation, not a defect; confirm the self-hosted runner does not repeat
   that limitation).
4. **Hosted-WM production lane** — `sh scripts/check/check-wm-production-fullscreen-evidence.shs`,
   under `xvfb-run` (confirmed to unblock the environment gate; see the bug
   doc's Xvfb note). **Mandatory first step:** `rm -rf $BUILD_DIR/native-cache
   $BUILD_DIR/hosted_entry` — the harness caveat is that it can serve a stale
   binary from `--cache-dir` even when source changed (verified: a rebuilt
   binary lacked newly-added string literals until the cache dir was
   deleted). Expected-green: progression past `windows-ready count=5` (already
   reached pre-fix) and past the current frontier inside
   `WebRenderPixelArtifactCache.request_to_pixel_artifact` with **no** `field
   access on nil receiver` crash from the Dict.get/Option-match shape. Full
   first-frame render is the ideal outcome but not guaranteed — the aggregate-
   return-nil half of the defect (distinct from Dict.get) is still
   layout-sensitive and only B1/A2 (not in this campaign) target it fully; a
   clean pass here proves the Dict.get portion, not the whole bug doc.
5. **SimpleOS freestanding/guest lane** — `sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
   (runs with `SIMPLE_BOOTSTRAP=1`, exercises the A1 nested-array-identity
   path directly). Expected-green: the rerun6-10 progression already landed
   (parser recovers DOM, sha256 digest path fixed, font/glyph chained-dispatch
   fixes) must still hold — this is a regression check, not new territory.
   Additionally watch for the **B2 warning** (`[mir-lower] WARNING: mutable
   array-typed module global ...`) firing on any remaining mutated array
   global on this path — its appearance is expected and correct (B1's real
   storage is not in this campaign), not a new bug; but if it fires where the
   `SIMPLE_STRICT_ARRAY_GLOBALS=1` variant is also run, confirm the build
   fails cleanly/loudly rather than corrupting silently.
6. **Non-regression showcase cells** — re-run
   `sh scripts/check/check-hosted-wm-capture-evidence.shs`,
   `sh scripts/check/check-responsive-showcase-evidence.shs`, and
   `sh scripts/check/check-widget-showcase-4k-200fps.shs` (the cells that
   already PASS per `doc/09_report/showcase_matrix_linux_x86_64_2026-07-26.md`
   / `showcase_matrix_fresh_evidence_2026-07-25.md`: widget×headless, 2D×headless)
   to confirm neither diff regresses working lanes.
7. **WM lanes from the worktree lane-runner** (`.claude/worktrees/lane-runner`) —
   re-run its evidence lanes after coordinating with whatever owns its
   in-flight state (§2); it already has a fresh
   `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-26.md` staged, so
   diff against that as the pre-campaign baseline rather than re-deriving one.

### 3d. Harness caveat (applies throughout §3c)

`rm -rf $BUILD_DIR/native-cache` (and `$BUILD_DIR/hosted_entry` where
applicable) before **every** smoke cycle that touches source, not just the
first. `check-wm-production-fullscreen-evidence.shs` only rebuilds when a
source file is newer than the binary AND reuses `--cache-dir` modules; a
source edit mid-campaign can be served stale otherwise (bug doc, "Harness
caveat" section).

---

## 4. Rollback plan

1. **Revert order (reverse of apply, §3a):** `dict_get_option_fix.diff`
   first, then `compiler_array_loss_fix.diff`. Rationale: the Dict.get/Option
   fix touches hot match-decode paths on both compiler lanes (higher blast
   surface even though it's fixes-only) and is the more likely source of a
   post-bootstrap regression (see report §6 residual risks — text-payload
   mis-decode, block-shape sensitivity). `compiler_array_loss_fix.diff`'s B2
   half is diagnostic-only (a warning, opt-in hard-fail) and A1 is scoped to
   one narrow pattern (nested-array element registration) — lower risk, revert
   second/only if it independently regresses something.
2. Because the two diffs are file-disjoint (§3a), either can be reverted
   independently without touching the other if only one causes a smoke
   failure.
3. If a specific smoke step regresses (§3c), bisect by reverting the
   higher-risk diff first and re-running just that smoke step before deciding
   whether the lower-risk diff is also implicated.
4. **A stage4 monitor-kill or `earlyoom` SIGTERM during bootstrap is not, by
   itself, evidence of a regression** (§2) — do not roll back the diffs on
   that basis alone; re-run with corrected headroom and confirm the failure
   reproduces on a clean-source stage4 before attributing it to these changes.
5. **Deploy gating (hard rule, do not bypass):** `bin/simple` /
   `bin/release/<triple>/simple` redeploy requires **explicit user approval**
   — this campaign produces `build/bootstrap/stage{3,4}/<triple>/simple`
   artifacts and smoke evidence; it does not swap the deployed binary itself
   under any circumstance without that approval. Per `.claude/rules/bootstrap.md`,
   never copy the Rust bootstrap binary to `bin/release/simple` either, even
   as an emergency stopgap, without recording a bug.

---

## 5. Success criteria

### Workaround sites and their un-conversion candidacy

| commit(s) | site(s) | root defect | fixed by this campaign? | un-convert now? |
|---|---|---|---|---|
| `457a435787d` | `theme_package._icons_to_css` (`contains_key`+bracket), `load_theme_package` cache, `_ui_theme_from_css` typed intermediates | exactly defect 1: `Dict.get()` + `match Some(x)` flat-payload loss | **Yes** — this is the Dict.get/Option match-decoder fix | **Yes**, after §3c step 2/4 are green: revert to plain `match icons.get(role): case Some(icon): icon.icon_id` and re-verify the hosted-WM lane still progresses |
| `39d3880cdd5` | `host_compositor_core._taskbar_render_input` (`active_wm_theme_id()` accessor), `simple_web_window_renderer` ×4 scalar accessors | general aggregate-return / Option-aggregate-return nil across the native ABI (layout-sensitive) | **No** — that fix (ABI-stable aggregate returns) is explicitly out of scope; bug doc's "Proper fix" section also says the accessor idiom is a legitimate API shape here, not only a workaround | No — keep as-is |
| (rerun7) tuple→two scalar projections (`cache_identity_generation`/`cache_identity`) | `font_renderer` (7 consumers) | tuple-return ABI loss | No | No |
| (rerun8) `FontRasterizer.invalid()` sentinel, loaders return plain struct | `FontRasterizer.load_selected_bytes` et al. | Option-aggregate-return nil (two-hop) | No | No |
| (rerun9/10) `present_fonts` binding, `owner.active[0]` direct read, i64-only `_engine2d_draw_ir_nth_int`, `char_code_at().to_i32()`→i64 sites (`draw_ir_adv.spl:126`, `simple_web_layout_engine2d_cpu.spl:17/21/29`, `host_gpu_draw_ir_event_flow.spl:54`, `glyph.spl:162`) | `Engine2D.draw_text` and siblings | chained-dispatch-on-erased-receiver class (tag-box landmine) | No | No |
| `a48cd24de91` (same-module globals handoff) | `_html_scan_events` → `parse_html` | array-global-loss = **half (b)**, needs **B1** (real storage) | **No** — B1 is not in this diff; B2 only makes the loss loud, it does not restore storage | No — keep the workaround |
| `fd6c5c552a8` (inline scan into `parse_html`) | same site | nested-array-return-loss = **half (a)**, exactly **A1** | **Yes** for the underlying defect | Reconsider only after host A/B verification (report's suggested 3-line `[[text]]` fixture, with/without `SIMPLE_BOOTSTRAP=1`, comparing `outer.len()` vs `outer[0].len()`) confirms A1 closes it in this exact freestanding shape — inlining may still be kept on its own structural merits even once not compiler-forced |
| `d8be76f670b` (sha256_text single-function rewrite) | digest path | array-return loss (same class as `[[text]]`) | Partially — depends on which specific array shape it hit | Re-verify after A1 lands before considering; not a blanket yes |
| `3b7a11b6cdf` | DrawIR font-asset root lookup nil-guard | interpreter `env_get` name-collision — **separate bug** (`interp_env_get_name_collision_nil_root_2026-07-26.md`), unrelated to both diffs | No | No — do not touch |

### Receipts to go permanently silent

- `AGG_MIN_FAIL probe=dict-get ...` / the interpreted-and-native
  `runtime error: field access on nil receiver` on the probe-3 shape —
  **must** go permanently silent (this is the campaign's core proof).
- The 15 `dict_get_option_match_spec.spl` assertions become permanently green.
- The `[web-parse] scan-handoff-loss returned=15 module=0` receipt is **not**
  expected to go silent from this campaign alone (that needs B1); if it does
  go silent, treat it as a signal worth investigating rather than an
  automatic win, since no storage fix landed to explain it.
- The new `[mir-lower] WARNING: mutable array-typed module global ...`
  receipt (B2) is **expected to start firing**, not go silent — its whole
  purpose is to surface the still-open storage gap loudly. It should only go
  silent once B1 lands in a future campaign.
