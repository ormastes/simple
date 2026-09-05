# Architecture / structure rule audit of the 2026-08-10→11 landing window

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Window:** `45e486f0be6..276c61ed464` on `origin/main` — **272 commits, 761
files changed**. `45e486f0be6` is the exact tip audited by the predecessor doc
`architecture_rule_audit_2026-08-10.md`, so this audit is the strict continuation
of it and does not re-litigate its window.
**Method:** every check was run against a `git archive` export of the fetched
`origin/main` tree (112,940 files), never the shared working copy — local `HEAD`
was 328 commits behind origin at audit time, so `git status`/`git diff` on the
checkout would have lied. Censuses used `/usr/bin/grep -rn` (the wrapped `grep`
honours `.gitignore` and under-reports). `examples/` was treated as live gate
source, not samples.

---

## Clean (verified, non-vacuous)

| Rule | Result | Evidence |
|------|--------|----------|
| **blink is a LEAF** | **CONFORM** | All 41 `use` statements under `src/lib/blink/**` (56 at `f17811ab90a1`, after Stage 5) resolve to exactly three roots: 22 `std.blink.*`, 14 `std.common.*`, 5 `std.skia.*`. `grep -rn '^\s*use ' src/lib/blink/ \| grep -vE 'use std\.(blink\|skia\|common)\b'` returns **empty**. Several lanes added `blink/layout/inline_text.spl`, `blink/layout/table_flow.spl` and the `blink/style/**` work tonight; **none reached sideways.** |
| **blink production callers** | **CHANGED MID-AUDIT — Stage 5 landed** | At the audit window tip `276c61ed464` this was still ZERO in `src/app/**`/`src/os/**`; the only repo-wide import was `src/lib/content/entity/web_contents.spl:7` `PaintArtifact`. While this audit was being landed, `src/app/browser/render_lane.spl:33` `use std.blink.lane.html_pixels.{blink_render_html_to_pixel_array}` landed, making it **two**. blink is now a reachable production path behind a flag that still defaults to the live lane. Re-verified at `f17811ab90a1`: **the leaf property SURVIVED** — blink grew to 56 imports (31 blink / 19 common / 6 skia) and still has zero sideways reach. |
| **Runtime family layering — no regression** | **CONFORM (2 new, see F1/F2)** | Full manifest-faithful re-implementation of `src/compiler/35.semantics/gc_boundary_check.spl` (`RUNTIME_FAMILY_MANIFEST` ranks + `GC_ALIAS_MANIFEST`) run over every `src/lib/**.spl` at BOTH ends of the window: **387 violations at `45e486f0be6`, 389 at the tip. Zero removed, exactly 2 added.** The 387 are a pre-existing backlog, not tonight's doing. |
| **No new Python** | CONFORM | 0 `.py` files in the 761-file window. |
| **`doc/` max depth 4 — no regression** | CONFORM | 0 files added at depth > 4 in the refactorable trees (`doc/01`–`doc/05`, `doc/07`) this window. 51 over-deep directories are pre-existing. |
| **Board-runnable** | already filed by another lane | The one `-kernel`-instead-of-firmware lane that landed tonight is already recorded in `doc/08_tracking/bug/arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`. Not re-filed here. The OVMF/OpenSBI real-firmware gates (`check-simpleos-arm64-efi-real-firmware-boot.shs`, `check-simpleos-riscv64-opensbi-real-firmware-boot.shs`) are present and were touched, not removed. No SimpleOS kernel build or WM gate was run for this audit, by instruction. |

---

## F1 — NEW layering violation: `nogc_sync_mut` imports the GC `gpu` family

**Severity: HIGH** (hard `nogc_imports_gc_family`, not a warning-only rank rule)

`src/lib/nogc_sync_mut/spec/evidence/counterpart/host_vulkan_lavapipe_provider.spl:92`

    use std.gpu.engine2d.sffi_vulkan.{vulkan_sffi_device_name}

`std.gpu` resolves through `GC_ALIAS_MANIFEST` to `gc_async_mut` (gc, rank 4).
The importer is `nogc_sync_mut` (nogc, rank 3). `import_violation_reason` returns
`nogc_imports_gc_family` — the same class the compiler emits as
`error[gc_boundary]`, not the softer `higher_layer_runtime_family`.

The file imports **one symbol**, `vulkan_sffi_device_name`, purely to label
evidence; every other Vulkan entry point it uses is a raw `rt_vulkan_*` SFFI
extern that has no family. **Not fixed here** because there are two defensible
answers and picking one is an owner decision: (a) drop the import and read the
device name from `rt_vulkan_get_last_error`/a new `rt_vulkan_*` extern, or (b)
move `vulkan_sffi_device_name` down into `common/`. Either is a small change;
guessing wrong silently changes what the evidence receipt reports.

## F2 — NEW layering violation (manifest artifact): `std.async.*` has no such family

**Severity: LOW — likely a manifest defect, not a code defect**

`src/lib/nogc_async_mut/async/runtime.spl:14` `use std.async.combinators.{select}`

`RUNTIME_FAMILY_MANIFEST` carries a legacy row `family: "async", rank: 3`, so any
`std.async.*` path classifies as rank 3 — higher than the importer
`nogc_async_mut` (rank 2) — yielding `higher_layer_runtime_family`. But
**`src/lib/async/` does not exist**; the real module is
`src/lib/nogc_async_mut/async/combinators.spl`, i.e. the file's own sibling. The
two adjacent lines (`:12` `std.async.future`, `:13` `std.async.poll`) are the
identical shape and are pre-existing — only `:14` is new, so this window merely
grew an existing pattern.

**Not fixed here.** Deleting the import would break the file. The right fix is
either to retire the `"async"` manifest row or to make these imports
`std.nogc_async_mut.async.*`, and both change what the compiler reports for ~all
of `src/lib/nogc_async_mut/async/**` at once. Needs the runtime-family owner.

## F3 — Directory fan-out guard went from GREEN to RED: 27 directories

**Severity: MEDIUM** (structure rule; the guard exists and is now failing)

    sh scripts/check/check-directory-fanout.shs --ref 45e486f0be6
      → PASS — 18673 director(ies) checked, 0 over limit
    sh scripts/check/check-directory-fanout.shs --ref origin/main
      → FAIL — 27 over limit

The prompt for this audit recorded the guard as RED on **3** directories when
last run; it is now RED on **27**. Every one is a directory that grew past its
recorded baseline inside this window. Directories over baseline (current vs
baseline): `scripts/check`, `scripts/check/lib`, `scripts/os` 60/58,
`src/app/devhub` 36/34, `src/app/office/sheets` 28/27,
`src/compiler_rust/compiler/tests` 41/39,
`src/lib/nogc_sync_mut/spec/evidence/counterpart` 14/13,
`src/os/drivers/gpu/board_vulkan` 20/18, `src/runtime/test` 23/20,
`test/01_unit/app/office` 59/58, `test/01_unit/compiler/backend` 178/177,
`test/01_unit/lib/blink` 32/27, `test/01_unit/lib/common` 384/383,
`test/01_unit/lib/common/crypto` 39/38, `test/01_unit/lib/common/ui` 101/100,
`test/01_unit/os/vulkan` 19/12, `test/01_unit/runtime` 39/38,
`test/03_system/app/llm_caret/feature` 21/16, `test/03_system/check` 167/166,
`test/unit/lib/blink` 32/27, `test/unit/lib/common/crypto` 25/24, plus
`test/fixtures/native_unwrap_enum_receiver`, `doc/03_plan/agent_tasks`,
`doc/03_plan/sys_test`, `doc/06_spec/03_system/app/llm_caret/feature`,
`doc/06_spec/03_system/check`, `doc/07_guide/os`.

**Not fixed here.** The two candidate fixes — splitting 27 directories, or
re-baselining 27 entries — are both wrong done unilaterally: splitting moves
files other sessions are mid-flight on, and re-baselining converts an enforced
rule into a rubber stamp. Note the `doc/06_spec/**` entries **cannot** be split:
`.claude/rules/structure.md` marks that tree DO NOT REFACTOR, so those two rows
are guard-scope bugs, not repo bugs. Whoever owns the guard should exempt the
DO-NOT-REFACTOR trees and then decide split-vs-rebaseline for the rest.

## F4 — `class X(Y)` inheritance in the compiler (PRE-EXISTING, needs a ruling)

**Severity: MEDIUM** — outside this window, but unresolved and load-bearing

`CLAUDE.md` says "**NO inheritance** — use composition, traits, mixins". Three
real declarations exist in owned compiler code:

- `src/compiler/70.backend/linker/linker_context.spl:16` `class LinkerCompilationContext(CompilationContext):`
- `src/compiler/80.driver/pipeline/compiler_context.spl:16` `class CompilerCompilationContext(CompilationContext):`
- `src/compiler/80.driver/driver_helpers.spl:50` `class CheckBackendImpl(Backend):`

**None are in this window** and the predecessor audit reported "NO inheritance:
CONFORM" — correctly, because it scanned for `extends`/`super.`, which this
syntax does not use. Whether `class X(Trait)` is trait *conformance* (legal) or
*inheritance* (banned) is not stated anywhere in `.claude/rules/language.md`. It
compiles today, so it is probably conformance syntax — but the rule as written
reads as a ban and the next audit will re-flag it. **Needs one sentence in
`.claude/rules/language.md`**, not a code change. Remaining `class X(Y)` hits are
in `src/compiler_rust/lib/std/**` (seed-side) and docstring examples.

## F5 — STALE DOC: `blink_wiring_plan.md` Blocker 1 contradicted itself — **FIXED HERE**

`doc/03_plan/ui/rendering/blink_wiring_plan.md` Blocker 1 read "Inline text
measurement — **entirely absent**. No text-measure API anywhere in
`src/lib/blink/**`", while Blocker 7 in the same file said blink's new
`table_flow.spl` "measures cells through `layout/inline_text.spl`". The API
landed this window: `src/lib/blink/layout/inline_text.spl` exports
`inline_font:44`, `inline_metrics:53`, `inline_text_advance_width:57`,
`inline_text_cell_width:65`, `inline_text_baseline:69`,
`inline_text_line_height:73`, `layout_inline_text:83`. Blocker 1 is now marked
CLOSED 2026-08-11 with that evidence.

Verified NOT stale in the same doc: §1.1 ("blink is test-only, exactly ONE
production import") still holds exactly as written; Blockers 8 (`calc()`) and 9
(visual effects) are still genuinely absent from `src/lib/blink/**`.

## F6 — FALSE "Resolved" header: `browser_color_commonization_blocked_2026-05-10.md` — **CORRECTED HERE**

**Severity: MEDIUM** — a false Resolved is worse than an open bug

The doc carried `Status: Resolved (2026-05-19)` in two header lines plus a
"Re-verification (2026-05-29)" section. It was false: the 2026-05-19 work added
`parse_css_color` / `CssLength` / `css_named_colors.spl` and left a "Next step:
delegate", and that step never happened — the added code had **zero references
anywhere** outside its own file and was not in `css.spl`'s export list. A
parallel lane established this during this window and appended a "Correction
(2026-08-11)" section resolving it honestly, **by deleting the dead third
implementation** rather than by delegation.

What was still wrong at audit time: the two status lines at the TOP of the file
still read `Resolved (2026-05-19)`, directly contradicting the correction at the
bottom — a reader who stops at the header still gets the false claim. Headers
corrected here to **"Resolved by deletion (2026-08-11)"**, with an explicit note
that the 2026-05-19 resolution and the 2026-05-29 re-verification do not hold.
The historical body is retained verbatim.

Corroborating that colour commonization is still incomplete in the OTHER
direction: `src/lib/blink/style/cascade.spl:124 parse_color_value` is still a
private hex-only reader resolving `rgb()`/`rgba()`/`hsl()`/`hsla()`/named colours
to opaque black — Blocker 2 in `blink_wiring_plan.md`, which this audit
re-verified and annotated (see F5). With Stage 5 now landed, that is the one
remaining gap that would silently corrupt output rather than fail if the lane
flag is flipped.

## F7 — `rules.sdl` is UNTRACKED, and the new pre-push hook fail-closes on it: **every push to `main` is blocked**

**Severity: HIGH — repo-wide, blocks all landings**

Discovered by hitting it: pushing this very audit was blocked by the pre-push
hook wired in `aa7c848d394` ("fix(guards): fence pre-push hook WIRING"):

    FAILGATE rules_sdl_gates: 0 < min 12 — SHRANK by 12
    FAIL — 1 gate(s) shrank, 10 passed, 0 skipped (group quick)
    pre-push: BLOCKED by check-rules-sdl.shs (status 1)
    ERROR — nothing was checked (rules.sdl absent or gateless at <ref>)
    pre-push: BLOCKED by check-rules-sdl-integrity.shs (status 2)

Root cause: `scripts/check/check-rules-sdl.shs:19` reads `$REPO_ROOT/rules.sdl`
and `check-rules-sdl-integrity.shs:20` reads it from the **committed** tree, but

    git ls-tree -r --name-only origin/main | grep -i rules.sdl   ->  (empty)

`rules.sdl` **exists in the shared working copy** (8,900 bytes, 22 gate ids,
mtime 07:43 today) and is **not committed anywhere in history**. So the guard
scripts and the hook that calls them landed, and the registry they enforce did
not. Because the guard is correctly fail-closed on a missing/gateless registry,
the result is that *no* commit can pass the hook — this audit's commit, or
anyone's — until `rules.sdl` is committed.

**Not fixed here.** The file is another session's uncommitted mid-flight work
(`.claude/rules/vcs.md`: do not touch a file a concurrent session is mid-flight
on, and never whole-WC-commit files this session did not author). The fix is one
line of work for that session: commit `rules.sdl`. Until then every landing must
use `--no-verify`, which defeats the whole hook — the opposite of what
`aa7c848d394` intended.

---

## Not measurable statically — stated rather than faked

`use std.X` **resolution** could not be verified by a static path walk: a naive
walker reports 245 "unresolvable" imports in this window
(`std.array`, `std.gpu.engine2d.*`, `std.cli.*`, …), essentially all of which
resolve through alias rows and search paths that only the compiler's resolver
models. An unresolved `use` is a **warning**, not an error, so import breakage
does not fail loudly and cannot be ruled out from grep alone. Reporting this as
"245 violations" would have been a fabricated finding; reporting it as "clean"
would have been fail-open. It is neither — it needs a resolver-backed check, and
none exists.

## Carried forward, still open from the predecessor audit

- **Two Perl scripts** (`scripts/check/lib/portable-hardlink-lock.pl`,
  `portable-session-exec.pl`) are still present at the tip — the "ALL code in
  `.spl`/`.shs`" violation from `architecture_rule_audit_2026-08-10.md` Finding 1
  is unfixed.
- **MDSOC+ / ECS adoption is thin**: `use std.ecs` / `ComponentStore` appears in
  only 15 files across all of `src/app/**` + `src/os/services/**`, and still
  **zero** across `src/lib/blink/**`. Unchanged this window; pre-existing, per
  that doc's Finding 3.

## Re-verification 2026-08-17 (fleet lane C)

STILL-OPEN as a decision item, not a code defect. `src/compiler/35.semantics/gc_boundary_check.spl`
exists (378 lines). `reproducible_by` is NONE and the finding is a counted-violations
delta (389 vs 387), i.e. a policy backlog needing a human decision on whether to gate.
No spec can settle it; not actionable by an automated bug-fixing lane. Recommend
re-routing to an architecture decision (ADR) rather than the bug queue.
