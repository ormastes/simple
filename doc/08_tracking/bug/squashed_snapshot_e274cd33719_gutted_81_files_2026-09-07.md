# `e274cd33719` is a squashed stale snapshot that gutted 81 files repo-wide

**Date:** 2026-09-07
**Status:** PARTIALLY REPAIRED — one file proven and restored; 14 more need per-file triage.
**Severity:** High — product code on `main` was silently rolled back, and the
rollback is invisible to every push guard, because a reverted file is
structurally perfect: correctly sized, non-conflicted, symbol-preserving, and it
compiles.

## What happened

**Correction (2026-09-07): this commit is NOT a merge.** Its title says "merge
all share-history worktree branches into main", but `git rev-list --parents -n1`
shows a **single parent** (`0fce018eda3`). It is a squashed snapshot. That
matters: there was no "side" for it to take, so this is not a merge-resolution
mistake — the commit simply overwrote `main` with an older tree. An earlier
draft of this record called it a stale-side merge; that framing was wrong,
though the mechanism and the evidence below are unchanged.

The sharpest measure is files it changed with **zero additions** — pure
deletions, repo-wide across `src/` and `examples/`, >20 lines each:

```
81 files, 6233 lines deleted with 0 added
```

This is NOT confined to the compositor. The largest are
`k26_axi_hp_bridge.spl` (357), `cursor.spl` (288), `chart.spl` (230),
`dma.spl` (225), `target.spl` (225).

Scoped to the three UI/compositor areas it changed **209 files**:

```
209 files changed, 9114 insertions(+), 16402 deletions(-)
```

A net loss of **7,288 lines**. For at least one file this was not a deliberate
deletion but a stale-side merge: content that already existed on `main` was
thrown away.

## The proof (one file, fully established)

`src/os/compositor/frame_pacer.spl` lost `struct FramePacerContract` and its
`me contract()`, and had `thread_sleep` reverted to `extern rt_sleep_ms`,
undoing `8df0aa41dc4` ("refactor(sffi): consolidate blocking sleep ownership",
2026-08-25).

```
FramePacerContract occurrences
  at 8df0aa41dc4   (2026-08-25, ancestor of main): 3
  at 0fce018eda3   (its parent):                     3
  at origin/main   (today):                        0
```

The symbol was present at the commit's **parent** and is absent after it. That
is the whole argument: it removed something `main` still had.

Effect: `frame_pacer_spec.spl` went to **0 passed / 6 failed**, every example
dying on `method contract not found`. Restoring the file byte-identically from
`e274cd33719^` returns it to **6 passed / 0 failed**, with no regression in
`compositor_decision_closure_spec.spl` (the only other consumer of FramePacer,
6/6 before and after).

## Why no guard caught it

This repo's pre-push guards check tree STRUCTURE: conflict trees, conflict-marker
text, file counts, test-tree divergence, `rt_*` symbol-set deltas, and whether C
parses. A stale-side merge produces a tree that passes every one of them. The
existing `check-runtime-api-regression-push.shs` would have caught a mass `rt_*`
deletion, but this removed a Simple `struct` and a `me` method, which no guard
tracks.

`.claude/rules/vcs.md` already names this exact failure mode under "Sync must
never clobber": *"a sync that reverts is worse than no sync."* The rule is
written for `chore(sync)` commits; this was a `chore: merge` commit, and nothing
enforced the rule.

## Second file proven and restored: `cursor.spl`

288 of 294 lines deleted with zero additions. The parent blob carries the full
cursor model, and that blob is unchanged from 2026-08-11 through 2026-08-27, so
restoring it loses no intermediate work. `cursor_shape_pipeline_spec` went
**0 passed / 13 failed -> 13 / 0**. Sabotage: moving the `IBeam` hotspot `x`
from 5 to 99 flips exactly the two examples that assert it; reverted. The only
two other importers are unchanged before and after (`gtti_spec` 16/8,
`compositor_spec` 4/28 — both red for unrelated, separately-triaged reasons).

## Known damage NOT repaired here

- **`dirty_rect`**: the same commit ADDED four spec examples using
  `DIRTY_REGION_MAX_RECTS` / `new_bounded` while `dirty_rect.spl` kept its old
  111 lines. Those symbols exist **nowhere in history**, so the spec half landed
  and the source half was dropped. This cannot be restored — it has to be
  re-authored.
- **`gui_entry_desktop.spl`** (arm64/riscv64/x86_64 baremetal entries): rewound,
  dropping `scanout_id: 1u64` that `e1b881c3ba2` had landed three days earlier.
  These are NOT pure deletions (arm64 is -196/**+132**), so a blind restore from
  the parent would discard 132 lines of unknown provenance. Needs an owner.

## Still to triage — 13 more files

Of the 209, **33 still carry the merge's version untouched**; 176 have been
modified since (possibly healed, not verified). Among the 33, these product
files show a net line LOSS and have not been touched since. **A net loss is not
by itself proof of a clobber** — the merged branch may have deleted some of this
deliberately. Each needs the same first-parent test applied above before any
restore.

| lines lost | file |
|---:|---|
| 288 | `src/os/compositor/cursor.spl` |
| 95 | `src/os/compositor/screenshot_compare.spl` |
| 95 | `src/os/compositor/hosted_wm_capture_evidence.spl` |
| 64 | `src/os/compositor/hosted_backend_winit.spl` |
| 62 | `src/os/compositor/shared_mdi_setup.spl` |
| 60 | `src/os/compositor/simple_gui_hosted_wm.spl` |
| 23 | `src/os/compositor/hosted_input_sdl2.spl` |
| 7 | `src/os/compositor/vulkan_present_damage_gate.spl` |
| 6 | `src/os/compositor/simple_web_qemu_panel.spl` |
| 6 | `src/os/compositor/simple_gui_window_renderer.spl` |
| 3 | `src/os/compositor/simpleos_wm_theme_bootstrap.spl` |
| 3 | `src/os/compositor/pixel_content_store.spl` |
| 3 | `src/os/compositor/host_services/headless_display_adapter.spl` |
| 2 | `src/os/compositor/browser_compositor_backend.spl` |

`hosted_wm_capture_evidence.spl` is worth doing first: it is the host-side WM
capture path, so a rollback there degrades the evidence lane itself.

## Reproducing the test for any one file

```sh
git rev-parse e274cd33719^:<file>      # content main had going in
git rev-parse e274cd33719:<file>       # content the merge produced
git log --oneline <branch-point>..e274cd33719^ -- <file>
```
If the third command lists commits whose content is absent from the second, the
merge took the stale side for that file.

## Suggested guard

A push-tier check that FAILs when a merge commit's result for a file is
byte-identical to an ancestor OLDER than its first parent, unless the commit
message records the rollback. That is the generalisation of the frame_pacer
proof and is cheap to compute.
