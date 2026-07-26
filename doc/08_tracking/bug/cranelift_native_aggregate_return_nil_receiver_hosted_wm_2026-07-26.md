# Cranelift native lane decodes aggregate/Option returns as nil receivers — hosted WM first frame dies site-by-site

- **ID:** cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26
- **Date:** 2026-07-26
- **Area:** native-build `--backend cranelift --entry-closure --mode dynload`
  (the hosted-WM production lane); compiler aggregate-return/Option lowering
- **Severity:** high — blocks the host-WM showcase cells and any first frame of
  the hosted compositor. The SimpleOS guest compositor shares this pipeline.
- **Status:** OPEN (systemic). Five consumer sites converted to the
  owning-module accessor idiom (each verifiably moved the crash); the next
  site is inside the web render artifact pipeline, where aggregates are
  passed pervasively — chasing further sites is the wrong fix.

## Shape of the defect

A function returning a struct aggregate (`ResolvedThemePackage`,
`WebRenderArtifact`, …) or an Option of one (`ThemeRenderSnapshot?`,
`Dict<K, StructV>.get`) is called across the native call ABI; the callee runs,
but the caller receives **nil**, and the first field access dies with
`runtime error: field access on nil receiver` (SIGILL after the message).

Confirmed instances, each isolated by receipt-probe bisection under Xvfb
(`sh scripts/check/check-wm-production-fullscreen-evidence.shs`):

| site | shape | fixed by |
|---|---|---|
| `theme_package._icons_to_css` | `match icons.get(role): case Some(icon)` → `icon.icon_id` | contains_key + bracket (`457a435787d`) |
| `theme_package.load_theme_package` cache | same `.get()` + match | same commit |
| `theme_package._ui_theme_from_css` | calls nested in struct-field position | typed intermediates (same commit) |
| `host_compositor_core._taskbar_render_input` | `if val snapshot = active_wm_theme_render_snapshot(): snapshot.id` | `active_wm_theme_id()` accessor (`39d3880cdd5`) |
| `simple_web_window_renderer` ×4 | `load_theme_package(t).fingerprint`, `.snapshot.material.*` | new scalar accessors in owning module (same commit) |

Next unfixed site: inside `WebRenderPixelArtifactCache.request_to_pixel_artifact`
(crash after receipt `c2`, i.e. past request construction, inside the render →
artifact pipeline, which returns/wraps `WebRenderArtifact` aggregates at every
stage).

## Key observations

- **Only the Some/present path faults.** The identical Option pattern binding
  in `host_wm_theme_bootstrap` survives at startup because no theme is
  installed yet (None); the first frame, with a theme installed, dies. Tests
  that exercise empty paths systematically miss this.
- **Layout-sensitive.** Adding print-only receipts inside `_px_int` moved the
  crash from the `_ui_theme_from_css` region to the r7/r8 region with no
  logic change — the mis-lowering depends on code layout, so single-site
  verdicts are unstable and A/B tests must re-run the oracle, not diff one run.
- **Interpreted lane is fine.** The same entry runs past all these sites under
  the stage3 interpreter (it stops later only for the missing
  `rt_winit_event_loop_new` extern, which is native-only by design).
- Origin already carries the same diagnosis in prose:
  `host_wm_theme_bootstrap.spl` — "Native package aggregates still cross the
  call ABI as a nil receiver" — and dodges `load_theme_package` at startup.

## Progression evidence (one run each, clean cache)

banner → theme-evidence → window-created → raster-backend →
`windows-ready count=5` → first frame crash. Each landed conversion moved the
crash strictly later; current frontier is the per-window content render
(`simple_web_content_frame_cached` → `request_to_pixel_artifact`).

## Harness caveat found while bisecting

`check-wm-production-fullscreen-evidence.shs` only rebuilds when a source file
is newer than the binary AND reuses `--cache-dir` modules; a source edit can be
served stale from the native cache (verified: rebuilt binary lacked newly
added string literals until the cache dir was deleted). Bisections must
`rm -rf $BUILD_DIR/native-cache $BUILD_DIR/hosted_entry` per cycle.

## Minimal repro + cross-lane reframe (2026-07-26, later same day)

`probes/cranelift_aggregate_return_min.spl` reduces the deterministic half to
14 lines: **struct-valued `Dict.get(key)` + `match ... case Some(hit)` +
`hit.field`** crashes with the production error; struct width is irrelevant.
Two decisive controls:

- The **Rust seed interpreter fails the identical probe identically** — this
  half is NOT cranelift-specific. It is the long-known "Dict.get() -> nil on
  present keys" defect (memory: `reference_interpreter_dict_and_value_quirks`;
  `mode.spl` carries the workaround comment), now with a deterministic repro:
  the match takes the Some arm with a **nil payload**.
- A text-valued `Dict.get` on a present key silently yields nil on both lanes
  (`hit=` / `hit=nil`) — silent corruption, worse than the crash.

Direct aggregate returns and Option-fn Some paths PASS in the minimal layout
(probes 1, 2, 4) yet crashed at hosted-WM scale — the aggregate-return half
remains layout-sensitive and is still only reproducible at scale.

So two defects share the symptom:
1. `Dict.get` Option-payload loss — deterministic, cross-lane (interp +
   cranelift native), minimal repro in hand. Fix belongs in the shared
   `Dict.get` lowering/Option-wrapping, both compilers.
2. Layout-sensitive aggregate-return nil across the native call ABI — still
   scale-only.

## Pinpoint diagnosis for defect 1 (Dict.get)

`src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:608`:

```
if method_name == "get":
    ...
    val field_value = val_struct_get_field(receiver, val_to_text(key))
    if field_value >= 0: return field_value   # raw value, NOT Some(value)
    return val_make_nil()                     # nil, NOT None
```

`get` never constructs Option encoding, while `match ... case Some(hit)`
decodes its scrutinee as an Option — so the Some arm fires with a nil/garbage
payload. The Rust seed interpreter exhibits identical behavior (probe-proven),
so it mirrors the same raw-or-nil contract. Any fix must either (a) wrap
`get`'s result in proper Some/None encoding in BOTH compilers plus the native
lowering, auditing `??`-based call sites that currently rely on nil-or-raw, or
(b) teach the match decoder to treat a raw non-Option scrutinee as
`Some(raw)`/`nil as None` consistently. Either way it is a semantic change to
Option runtime encoding — bootstrap + extended smoke matrix required before
deploy (see `.claude/memory` stage-4 rollback precedent).

## SimpleOS guest parser instance (2026-07-26, rerun4)

The guest WM render collapse (`degenerate-parse html_len=5794 nodes=1
split_parts=18 lt_portable=17 rules=0`) fits this class: the per-part receipt
dump proved the document well-formed (doctype, 663-byte `<html>` attribute
payload, head/meta/title, 4,786-byte style, body, two divs), every scanner
bail/divergence receipt stayed silent, yet `parse_html` built only the bare
`#root` — consistent with `_html_scan_events`'s nested-array `[[text]]`
return being lost across the call boundary, sizing the arena from zero
events. `rules=0` with a valid outer struct fits the layout-sensitive
character: inner `[text]` helper returns collapse to empty while the outer
aggregate survives. Mitigation landed: the scanner now hands events to
`parse_html` via same-module globals plus a scalar count, with a
`[web-parse] scan-handoff-loss` cross-check receipt and a
`degenerate-arena`/`degenerate-event` dump if events arrive but none make a
node (`simple_web_html_layout_renderer_foundation.spl`).

**Rerun5 receipt — CONFIRMED, and the globals fallback fails too:**
`[web-parse] scan-handoff-loss returned=15 module=0`. The scanner produced
exactly 15 events (hand-count of the part dump agrees: 15 tag events for
this document — the scan logic is fully correct in the guest), the scalar
i64 return survived the call boundary, but the **same-module `[text]`
global arrays read back 0 entries**. So in the freestanding SimpleOS build
BOTH cross-function channels for array data lose it: nested-array `[[text]]`
returns AND array-typed module globals (the latter contradicts the host-lane
fix in 952d2ca34d7 — that fix does not cover this build). Builtin returns
(`split`) and locals are the only proven channels. Second mitigation: the
scan is now INLINED into `parse_html` (it was the only caller) so the event
arrays are locals and never cross the ABI.

## Proper fix

In the cranelift lowering: make aggregate returns (direct and Option-wrapped)
ABI-stable regardless of layout — not more caller-side accessor conversions.
The accessor idiom is a legitimate API shape for the theme modules, but the
web render pipeline passes aggregates by design and should not be rewritten
around a codegen defect.

## Related

- `doc/08_tracking/bug/interp_env_get_name_collision_nil_root_2026-07-26.md` — different defect, same session, also nil-from-infrastructure
- `.claude/memory` `reference_jit_option_i64_value3_none_collision` — earlier Option-decode defect in the JIT lane
- Xvfb note: with `xvfb-run` the host-WM lane is NOT environment-blocked — hooks ready, WM launches, 5 windows created; the blocker is this defect.
