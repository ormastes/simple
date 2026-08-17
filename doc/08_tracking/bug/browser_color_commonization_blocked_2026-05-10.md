# Browser Color Parsing Commonization Blocked

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Date:** 2026-05-10
**Component:** browser_engine/dom.spl, common/color/
**Severity:** Low (tech debt)
**Status:** REOPENED 2026-08-11 — partially resolved (was falsely "Resolved (2026-05-19)")

## Problem

`src/lib/gc_async_mut/gpu/browser_engine/dom.spl` contains ~500 lines of CSS color
parsing (lines 1048-1700) that partially duplicates `src/lib/common/color/convert.spl`.
Cannot consolidate due to three blockers:

## Blockers

### 1. Cranelift f64? Optional Bug
dom.spl uses manual integer parsers (`pcc_parse_int`, `hex_byte`, `hex_nibble`,
`hex_digit`) that return concrete types instead of `f64?` optionals. This works
around a known Cranelift codegen bug with `f64?` in compiled mode. Switching to
common/color functions that return `Color?` or use optional intermediates would
hit this bug.

### 2. u32 vs Color Type Mismatch
- Browser engine uses packed `u32` RGBA throughout (0xRRGGBBAA)
- Common library uses `Color(r: i64, g: i64, b: i64, a: i64)` struct
- Every color callsite in the browser would need conversion wrappers

### 3. Named Color Table Size
- dom.spl: 148 CSS Level 4 named colors (full spec)
- common/color/convert.spl: 25 named colors
- Would need to expand common table to 148 entries to avoid regression

## Resolution (2026-05-19)

All three blockers resolved without waiting for the Cranelift f64? fix:

1. **Blocker 1 — Cranelift f64? bug**: Worked around by using pure integer arithmetic
   throughout `parse_css_color`. No `f64?` optionals anywhere in the color parse path.

2. **Blocker 2 — u32 vs Color type**: Resolved by:
   - `parse_css_color` in `css.spl` returns `i64` (ARGB packed, same bit layout as engine2d u32)
   - `Rgba8.to_u32()` / `Rgba8.from_u32()` added to `common/engine/color.spl`
   - Browser code can call `parse_css_color` then pass the i64 directly to renderer

3. **Blocker 3 — named color table**: `css_named_color` in `css_named_colors.spl` covers CSS Level 4
   (148 unique names including `rebeccapurple`; grey/gray synonyms handled via `or` branches;
   `css.spl` normalizes input with `.trim().to_lower()` before calling the table).

**Files changed:**
- `src/lib/gc_async_mut/gpu/browser_engine/css.spl` — added `parse_css_color`,
  `css_color_r/g/b/a`; delegates named-color lookup to `css_named_colors.spl`
- `src/lib/gc_async_mut/web/css_named_colors.spl` — `css_named_color` with 148 CSS L4
  names (grey/gray synonyms via `or` branches; input normalized via `.trim().to_lower()`)
- `src/lib/common/engine/color.spl` — added `Rgba8.to_u32()` and `Rgba8.from_u32()`

**Next step:** When color parsing is added to `dom.spl`, delegate to `parse_css_color`
from `std.gc_async_mut.gpu.browser_engine.css`.

## Re-verification (2026-05-29)

Confirmed all three blockers resolved:
- `parse_css_color` / `css_color_r/g/b/a` present in `css.spl` (186 lines)
- `Rgba8.to_u32()` / `Rgba8.from_u32()` present in `common/engine/color.spl`
- `css_named_colors.spl` covers 148 unique CSS L4 names (grep -oE '"[a-z]+"' | sort -u | wc -l = 148)
- `dom.spl` reduced to 124 lines; manual parsers (`pcc_parse_int`, `hex_byte`, etc.) absent
- `css.spl` calls `.trim().to_lower()` before `css_named_color()` — case normalization confirmed

## Correction (2026-08-11) — the 2026-05-19 "resolution" was never wired

The 2026-05-19 resolution added `parse_css_color` to `css.spl` and a 148-name
`css_named_colors.spl`, and left a "Next step: delegate to `parse_css_color`".
That next step never happened. Measured 2026-08-11:

- `parse_css_color`, `parse_css_length`, `css_length_to_px`, `css_color_r/g/b/a`,
  `CssLength`, and the `css_px_*` arithmetic helpers in `css.spl` had **zero
  references anywhere** in `src/`, `test/`, `examples/`, `doc/` outside their own
  file. None were in `css.spl`'s `export` list either.
- The LIVE color path is `browser_engine/dom_color.spl`
  (`parse_color_value` / `parse_hex_color` / `named_color_to_u32`), reached from
  `dom_color_named.spl`, `dom_visual_effects.spl`, `render_fixtures.spl`. It is a
  strict superset: hsl/hsla, modern space-separated syntax, `currentColor`,
  comment stripping, and a **149-name** table that contains every one of
  `css_named_colors.spl`'s 148 names plus `transparent`.

So the commonization did not merge two implementations — it added a third, dead
one. Removed the dead side instead: the `parse_css_color`/`CssLength`/`css_px_*`
block in `css.spl` (270 → 87 lines) and `src/lib/gc_async_mut/web/css_named_colors.spl`
(144 lines, sole caller was the dead parser). `CssPx` and all exported symbols
are untouched. Importer specs byte-identical before/after (`css_ext_routing` 3/9,
`float_layout` 13/10, `ui.chromium/css_spec` 9/3 — all pre-existing reds;
`layout_coverage_closure` 13/13 green).

Status corrected to: **Resolved by deletion of the redundant lane**, not by
delegation.

## Correction (2026-08-11, later) — the type analysis, and a first real wiring

The correction above is right that the 2026-05-19 resolution was never wired, but
its verdict ("Resolved by deletion of the redundant lane") is still not the whole
story: it disposed of the *dead* lane and left the *live* duplication untouched.
The surviving shared extraction is **`src/lib/common/color/css.spl`**, and the
reason nobody adopted it is a type mismatch, not neglect.

### The real type story (measured 2026-08-11)

`common/color/css.spl` answers `Color?` — a struct of four `i64` channels, plus
`nil`. Every live browser consumer is `u32`-typed. Comparing what each carries:

| | `Color?` | `u32` |
|---|---|---|
| RGB channels | yes | yes |
| Alpha | yes (`a`) | yes (packed) |
| **Parse failure** | **yes (`nil`)** | **no** |

So `u32` does **not** lose alpha — the 2026-05-10 report's framing of this as a
straight "u32 vs struct" impedance problem was incomplete. The one thing `u32`
cannot represent is **failure**, and that is exactly where the live lanes go
wrong. `dom_color.parse_color_value` ends in `?? 0x000000FF` — **opaque black for
anything it does not understand** — the same wrong-value-not-failure pattern as
blink's colour path, and invisible to any smoke test. (`dom_color.spl` does also
expose `parse_color_value_checked -> u32?`, which keeps the failure; the
unchecked entry point is the defective one.)

The adapter therefore must **not** provide a `Color? -> u32` that substitutes a
colour. It provides `Color -> u32` only, and callers unwrap explicitly.

### The finding that made a naive adapter unsafe

The "u32 family" is **not one convention — it is two**:

- `0xRRGGBBAA` — `gpu/browser_engine/dom_color.spl`
- `0xAARRGGBB` — `simple_web_css_box_effects.spl`,
  `simple_web_engine2d_renderer.spl`,
  `simple_web_html_layout_renderer_foundation.spl` (`argb()`)

A single unnamed `to_u32()` would have silently channel-swapped half the call
sites — a wrong pixel, not a crash. Both orders are therefore named explicitly:
`Color.to_argb_u32()` and `Color.to_rgba_u32()` in
`src/lib/common/color/types.spl`. No new module and no new parser was added.

### Wired (1 of 8 call sites)

`_box_shadow_hex_color` in `simple_web_css_box_effects.spl` now delegates to
`std.common.color.css.parse_hex_color` and packs with `to_argb_u32()`. It was
chosen because its contract is already `(bool, u32)` — it **has somewhere to put
a failure**, so the `nil` survives the adaptation instead of collapsing to a
substituted colour. 37 lines of hand-written hex parsing (plus its private
`_box_shadow_is_hex_digit`) deleted.

Evidence: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl`
is unchanged and already pins `#0000`, `#11223344`, `#12gg00` and `#000000000`
through this exact path. Measured **5 passed / 2 failed both before and after**
the change (baseline captured by reverting the edit and re-running) — the 2 are
pre-existing reds unrelated to colour. New spec
`test/01_unit/lib/common/color/color_pack_u32_spec.spl` pins both byte orders,
the parity values recomputed from the deleted parser's own arithmetic, and the
failure cases as `nil` rather than black.

### NOT wired, with per-site reasons

| site | why not |
|---|---|
| `dom_color.parse_color_value` | **Hex branch now delegates** (via `parse_color_value_checked`, see below). The remaining gap is its `?? 0x000000FF` fallback, which is a behaviour change to remove rather than a wiring step, and its `currentColor` black sentinel, which the shared parser declines by design. Needs the caller taught to handle `nil` first. |
| `dom_color.parse_hex_color` | Now has **no in-repo callers** — the delegation at `parse_color_value_checked` replaced its only one. Left in place rather than deleted because it is `pub` API surface; it is a live footgun (`hex_byte` answers a value for non-hex input, so `#gg` returns opaque black) and should be deleted in a follow-up that confirms no out-of-tree caller. |
| `foundation.parse_color` / `parse_color_any` | Conflate failure and `transparent` — both answer `0u32`. Also its named table is **wrong**: `red` is `(220,50,50)`, not CSS `(255,0,0)`. Correcting that changes rendering and needs its own change with its own evidence. |
| `foundation.parse_color_alpha` | Built on `parse_color_any`; blocked behind it. |
| `engine2d._hex_color_at` | Takes an explicit `fallback: u32` and parses at an offset inside a larger string rather than a whole token. Adaptable, but the offset-slicing is the real work, not the colour parsing. |
| `style/supports._supports_hex_color` | A validity predicate, so failure is representable — but it currently rejects uppercase `A-F`, which the shared parser accepts. Migrating silently fixes a bug; that should be its own change so the fix is visible. |
| `blink/style/cascade.spl` | Owned by a concurrent session giving blink parity via `common/**`. Not touched. |

## Correction (2026-08-11, third) — second call site wired, and the loss measured

`dom_color.parse_color_value_checked`'s `#` branch now delegates to
`std.common.color.css.parse_hex_color` and packs with `to_rgba_u32()`.

**The information-loss question, answered by measurement.** A probe compared the
local `parse_hex_color` against the shared one across 23 valid forms
(`#RGB`/`#RGBA`/`#RRGGBB`/`#RRGGBBAA`, both letter cases): **identical u32 for
every one, 0 mismatches**. On six invalid inputs (`#gg`, `#gggggg`, `#zzz`,
`#12345`, `#1`, `#`) the local parser returned `255` — `0x000000FF` — for all
six. That is bit-for-bit the same u32 as a genuine `#000000`.

So `u32` is the impoverished side, and the loss is specifically the **failure
case**, not alpha (both carry 8 bits of alpha). A caller holding a `u32` cannot
distinguish "black" from "I did not understand that". This is why
`common/color/types.spl` deliberately offers no `Color? -> u32` helper that
substitutes a colour for `nil`: such a helper would paint a wrong pixel that no
smoke test can see, which is the original defect, not a fix for it.

Because `parse_color_value` wraps the checked form with `?? 0x000000FF`, the
unchecked entry point's observable behaviour is **unchanged** for every input,
valid or not — no existing caller moves. Only `parse_color_value_checked` gains
a truthful failure signal.

Evidence:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl`
— 19 assertions, `executed=19 passed=19 failed=0`, covering parity on supported
forms, `nil` on unsupported ones, the aliasing of `#gg` with `#000000` in the
`u32` channel, and the untouched named/`rgb()`/`var()` branches. Sabotaging the
delegation's byte order (`to_rgba_u32` → `to_argb_u32`) turns 8 of the 19 red,
so the spec is not a tautology.

`dom_color_alpha_normalization_spec.spl` is 2/3 both before and after the change
— that red is pre-existing and unrelated.

### Status

**REOPENED — partially resolved.** Not "Resolved (2026-05-19)", and not fully
resolved by the deletion recorded above either. What is true: the dead third
implementation is gone, the shared parser is rich and specced, the adapter now
exists, and **2 of 8** live call sites are migrated with before/after evidence.
Six remain, each for a recorded reason above. The bug closes when they are
migrated or explicitly declared out of scope — not before.

## Related
- Timing commonization: completed (commit 6c07c3d)
- Layout commonization: blocked by i32/i64 + DOM-coupling architectural mismatch
- Unwired-extraction audit: `unwired_extractions_audit_2026-08-11.md` (instance 3)
