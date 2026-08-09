# WM lane rung (d): the guest renders the theme sheet with `var()` UNRESOLVED — two admission terms fail, not one

- **ID:** wm_guest_css_var_unresolved_blocks_material_admission_2026-08-09
- **Status:** OPEN
- **Severity:** high (true blocker for SimpleOS x86_64 WM lane rung (d))
- **Found by:** host-side reproduction of the 2026-08-08 lane serial log, 2026-08-09
- **Lane:** `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
- **Supersedes the root cause of:**
  `doc/08_tracking/bug/wm_window_bg_layers_reject_cpu_composited_material_2026-08-08.md`

## Summary

The 2026-08-08 writeup concluded that `mat_layers == ""` was **the single**
failing term of the `engine2d-cpu-composited-material-v1` admission predicate,
caused by the `aetheric_dark` theme giving `.wm-window` a two-layer background.

That is **wrong**, and acting on it (either "composite the gradient layer into
the material" or "drop the gradient from the theme") would not have unblocked
the lane.

All three material values in the guest serial log are the exact signature of
**CSS custom properties (`var(--…)`) not being resolved** in the sheet the guest
renders. One upstream defect produces all three.

## Proof (host reproduction, exact match on all three numbers)

Guest serial log (`build/wm_lane_evidence/runB_2327_iso_timeout420s/serial.log`):

```
[web-style-producer] entry-rejected index=4 mode=engine2d-cpu-composited-material-v1 \
    bg=352321535 gf=0 gt=0 layers_len=73 backdrop_len=21 animation=none
```

Host probe through `simple_web_layout_debug_style_by_id`, feeding the two
`aetheric_dark` declarations with **no `:root` custom-property block in scope**:

```
backdrop-filter: blur(var(--blur-surface)) saturate(170%);
background: linear-gradient(180deg, rgba(255,255,255,0.08), rgba(255,255,255,0.025)), var(--app-surface);
```

```
novar layers_len=73 backdrop_len=21 bg=352321535
novar backdrop=[blur() saturate(170%)]
novar layers=[linear-gradient(180deg, rgba(255,255,255,0.08), rgba(255,255,255,0.025)),]
```

`bg=352321535`, `layers_len=73`, `backdrop_len=21` — **all three identical to
the guest**. Feeding the *same* declarations **with** the `:root` block present
gives `layers_len=93` and a resolved `rgba(31,31,33,0.80)` base layer, i.e. a
different signature from the one the guest reported. `layers_len=73` is
`linear-gradient(...)` **plus a bare trailing comma** — the empty second layer
left behind when `var(--app-surface)` expands to nothing.

## What this refutes

1. **`mat_layers` is not the only failing term.** `backdrop_len=21` is
   `blur() saturate(170%)`, not a healthy `blur(30px) saturate(170%)` (25
   chars). Directly measured:

   ```
   BD unresolved_admitted=false resolved_admitted=true
   ```

   `simple_web_backdrop_admission` requires the blur term to end in `px)`;
   `blur()` does not, so `backdrop.admitted` is **false**. The 2026-08-08 table
   scored this term "pass" from the length alone, without evaluating it.

2. **`bg=352321535` is not the theme's surface colour.** `0x14FFFFFF` is the
   gradient's *first stop* (`rgba(255,255,255,0.08)`), picked up by
   `parse_color_alpha` scanning the malformed shorthand. The intended
   `--app-surface` is `rgba(31,31,33,0.80)` = `0xCC1F1F21`. The window is
   currently attesting a surface colour it never had.

3. **Neither proposed fix would have worked.** Compositing-and-digesting the
   gradient layer (option A) or removing it from the theme (option B) both
   leave `backdrop.admitted == false`, because `--blur-surface` is dead for the
   same reason. Option B would additionally have changed the Aetheric visual
   design for no gate benefit.

## Where the real defect is

`extract_css` (`simple_web_html_layout_renderer_core.spl`) resolves `var()` in
two steps: `_css_collect_custom_props` (line 122) harvests `--name: value` from
`:root` blocks across every `<style>` block, then `_css_resolve_vars` (line 216)
substitutes. On the host, driving the **generated snapshot's own**
`composed_css` (`src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl`,
which does define `--app-surface` and `--blur-surface` in a `:root` block)
resolves correctly. In the guest it does not.

### Mechanism, confirmed

`_css_resolve_vars` splices an **undefined** custom property (no fallback) out
to the **empty string** at top level and still returns `Resolved`. In the
`replacement_text` match, the `CssVarResolution.Invalid` arm returns early only
`if nested`; at `nested == false` it falls through with
`replacement_text = ""`. CSS requires a declaration containing an unresolvable
`var()` to be *invalid at computed-value time* (dropped), never substituted
empty. Substituting empty is what manufactures `blur() saturate(170%)` and
`linear-gradient(...),` — syntactically parseable, semantically wrong values
that then fail the material gate looking like a content mismatch.

This was pinned down by a diagnostic that **failed open first**: a post-hoc
`css.index_of("var(") >= 0` check on the resolved sheet did not fire on a
sheet whose variables provably did not resolve — because the `var(` text is
gone, replaced by nothing. The receipt was moved to the substitution site and
now reports the offending property by name:

```
[web-style-producer] css-var-undefined name=--blur-surface props=0 depth=0
```

Verified both directions: fires on the known-bad sheet, silent (0 lines) on the
same declarations with the `:root` block in scope.

### Still open: why the property is undefined in the guest

The remaining unknown is why `props=0` / the lookup misses in the guest when
the generated snapshot's `composed_css` does define both properties. Candidate
mechanisms, in the order they should be probed:

- `_css_resolve_vars` degrades **silently**: the substitution scan is capped at
  `vg < 400` per pass and simply `break`s, emitting the unscanned tail raw; a
  `state.remaining <= 0` (`CSS_VAR_SUBSTITUTION_BUDGET = 1024`) returns
  `BudgetExceeded`, and the caller (line 739) then falls back to **`css_raw`**,
  i.e. the entire sheet unresolved. Both paths are indistinguishable from
  "no custom properties" downstream.
- `_css_collect_custom_props` capacity: `:root` block scan capped at 200,
  entries at 400, and `CssVarResolutionState.new` parses at most **200**
  properties.
- Guest-only divergence in the native/freestanding lowering of the
  byte-slicing/`find_from` code in those two functions (the theme sheet reaching
  the guest is not necessarily byte-identical to the snapshot literal —
  `apply_simpleos_css_theme_override` / `theme_render_snapshot_with_wm_colors`
  append a second `:root` projection).

## Next step

The two receipts (`css-var-undefined`, `css-var-pass-bailed`) were written and
verified in the working copy but are **NOT landed**: at push time the shared
working copy's `simple_web_html_layout_renderer_core.spl` also carried an
unrelated in-flight change from another session (it removed the `#text`
no-author-candidate rule and its CSS 2.1 6.2 rationale, which `main` has), so
committing that blob would have reverted someone else's fix. Re-apply the two
receipts on top of origin's version before landing them — the exact code and
placement are described above. Then re-run the lane with
`SIMPLEOS_WM_READINESS_TIMEOUT_MS=420000`; the serial log will state, in one
line, which property is undefined and how many the guest collected — separating
"no properties collected" from "budget/depth bail" from "collected but the
lookup missed", without another guess.

Then fix the substitution semantics (drop the declaration instead of splicing
empty). Note that fixing the semantics alone will not turn the lane green: it
converts a wrong-value pass into a correctly-dropped declaration, which the
material gate still (correctly) refuses. The guest must actually resolve
`--app-surface` and `--blur-surface` for rung (d).

### Host-probe caveat

`WEB_RENDER_BUDGET_MS` is 10000 and, per the note atop
`simple_web_html_layout_renderer_foundation.spl`, an interpreted `bin/simple
run` routinely blows it on a full theme sheet — the render then degrades and
every computed style reads back as 0. Observed directly: the same full-sheet
probe returned `layers_len=93` on one run and `layers_len=0` on the next. Small
two-declaration probes are stable; **do not draw conclusions from a full-sheet
host probe without `SIMPLE_WEB_RENDER_BUDGET_MS` raised.**

## Lane invocation note (unchanged, still required)

`READINESS_TIMEOUT_MS` defaults to 60000; the lane runs QEMU **TCG** (no `accel`
passed even though `/dev/kvm` is usable), ~30x slower, so the default truncates
the boot mid-frame and reports a misleading
`dynamic-scanout-or-desktop-readiness-missing`. Use
`SIMPLEOS_WM_READINESS_TIMEOUT_MS=420000`.

## 2026-08-09 update — substitution semantics FIXED; leading root-cause hypothesis named

### Landed (build-free, unit-verified)

`_css_resolve_vars` no longer splices an unresolvable `var()` out to the empty
string. This resolver is driven over a WHOLE `<style>` sheet, not one
declaration, so "drop the declaration" cannot be expressed by returning
`Invalid` (that would drop the entire stylesheet). The fail-closed equivalent at
this granularity is to leave the **`var(...)` source text verbatim** in place:
downstream value parsers cannot parse a literal `var(`, and
`src/os/compositor/simple_web_window_renderer.spl:242-248` already states the
intent — it keeps "unresolved variables as rejection witnesses". The declaration
now fails loudly instead of attesting a colour it never had.

Counted and diagnosable, not silent. Two receipts, both silent on a healthy
sheet:

```
[web-style-producer] css-var-unresolved count=N first=--app-surface idx=-1 props=P sw_raw=B1 sw_portable=B2 css_len=L
[web-style-producer] css-var-pass-bailed block=G props_len=P css_len=L
```

`css-var-unresolved` is emitted at the substitution site (a post-hoc
`index_of("var(")` on the caller side FAILS OPEN — verified). It separates the
three candidate mechanisms in one line:

| reading | meaning |
|---------|---------|
| `props=0` | `_css_collect_custom_props` collected nothing — no `:root` reached the guest |
| `props>0, idx=-1`, `sw_raw=true` | collected, but the name lookup missed (cascade/ordering/capacity) |
| `sw_raw=false, sw_portable=true` | x86_64 freestanding boolean mis-marshalling (see below) |
| `css-var-pass-bailed` present | the whole pass bailed and the sheet is used RAW (a different failure) |

### Leading hypothesis for the guest-only divergence: `text.starts_with` at depth

**`_css_resolve_vars` was the one remaining freestanding-unsafe predicate on
this path.** Its var-name validity test was

```
val valid_var_name = (prop_name.len() > 2 and prop_name.starts_with("--"))
```

`doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md` **residual
item 3 (still OPEN)** records that on the x86_64 freestanding native build
`text.starts_with(literal)` called from a DEEP frame returns the wrong value
(and can corrupt control flow); the identical call in a shallow frame is always
correct. That exact defect already "collapsed `_html_scan_events` to zero events
in the guest while the host produced a full DOM"
(`simple_web_html_layout_renderer_foundation.spl:449-456`), which is why
`text_matches_at` / `text_starts_with_portable` exist — they compare plain
integers so no boolean crosses a runtime text-builtin boundary.

`_css_resolve_vars` sits deep inside the style pass **and recurses**. A
mis-marshalled `false` there makes `valid_var_name` false for EVERY custom
property, which takes the `Invalid` arm and (under the old semantics) spliced
every `var()` away — reproducing `layers_len=73`, `backdrop_len=21`,
`bg=0x14FFFFFF` exactly, with `props` still non-zero.

This also explains why collection is NOT the failing half: trace
`_css_collect_custom_props` with `starts_with` stuck at `false` and it still
works — `_css_root_prefix_is_preamble("")` returns via `remaining.len() == 0`
without ever calling `starts_with`, and `between.starts_with("[")` is guarded by
`if between.len() > 0`, which is false for a bare `:root`. So the property table
is populated (45 entries from `aetheric_dark`) while every lookup is rejected
before it happens.

The call site now uses `text_starts_with_portable`, which is the documented
freestanding-safe form and correct on both engines. **If this hypothesis is
right, that one-line change alone unblocks the vars in the guest.**

### What is NOT yet proven, and exactly how to settle it

Confirming this needs the guest — it cannot be measured on the host, where
`starts_with` is correct by construction. Resume with:

```bash
SIMPLEOS_WM_READINESS_TIMEOUT_MS=420000 \
  sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Read the serial log:

- **No `css-var-unresolved` line at all, windows admitted** → hypothesis
  confirmed, rung (d) reached.
- `css-var-unresolved ... sw_raw=false sw_portable=true` → hypothesis confirmed
  as the mechanism, and any remaining rejection is downstream of the vars.
- `css-var-unresolved ... props=0` → hypothesis REFUTED; the `:root` blocks are
  not reaching `_css_collect_custom_props` in the guest. Probe
  `_extract_css_vw_with_rule_limit`'s `<style>` pre-pass next.
- `css-var-unresolved ... props>0 idx=-1 sw_raw=true` → hypothesis REFUTED;
  collection works and the name lookup misses. Probe the entry text built in
  `_css_collect_custom_props` (name/value trimming) against
  `CssVarResolutionState.new`'s line parse.
- `css-var-pass-bailed` → a wholesale bail; the sheet is raw and the budget
  caps are the lead.

Alternatives NOT ruled out by host measurement (they are guest-only by nature
and the receipt above is what distinguishes them): sheet truncation by a
guest-side size cap, cascade-order divergence, and a native lowering difference
in the byte-slicing of either function. What IS ruled out on the host: the
theme file is present and its `composed_css` defines both `--app-surface`
(`rgba(31,31,33,0.80)`) and `--blur-surface` (`30px)`) in base `:root` blocks,
and the guest window sheet is that same `composed_css`
(`simple_web_window_renderer.spl:114,131-132`), so "the theme isn't in the
image" and "custom-property registration is host-only" are both false.

Also ruled out for the recorded run: render-budget exhaustion. The
2026-08-08 serial log contains **no** `[web-style-producer] budget-break` line,
so the style pass ran to completion.

### Regression guard

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.spl`
(8 examples). Sabotage-verified by restoring the empty splice: 8 total / 8
passed / 0 failed → 8 / 4 / 4 → 8 / 8 / 0.
`core_coverage_closure_spec.spl` had two assertions that pinned the old
splice-to-empty behaviour; both were updated to the fail-closed expectation with
the rationale inline (60 / 60 / 0).

## Do NOT

- Do **not** relax `mat_layers == ""` or the backdrop admission. Both are
  correctly rejecting a sheet whose variables did not resolve — that is the
  fail-closed behaviour working as designed, and
  `src/os/compositor/simple_web_window_renderer.spl:242-248` states the intent
  explicitly ("keeps arbitrary image stacks or **unresolved variables as
  rejection witnesses**").
- Do **not** change the `aetheric_dark` theme. The theme is fine; the sheet is
  being rendered with dead variables.

## Related

- `doc/08_tracking/bug/wm_window_bg_layers_reject_cpu_composited_material_2026-08-08.md`
  (root cause superseded by this record)
- `doc/08_tracking/bug/2026-08-05_wm_content_frame_web_provenance_unreachable_via_widget_panel.md`
