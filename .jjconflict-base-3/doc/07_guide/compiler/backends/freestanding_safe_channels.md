# Freestanding/native-safe data channels — what survives the call ABI and what does not

Status: living document, from the 2026-07-26 showcase campaign (12 landed
fixes; QEMU guest WM now presents frames; hosted-WM first frame survives).
Root bug: `doc/08_tracking/bug/cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`
(includes the compiler-side RCA with file:line pinpoints). The compiler fix
drafts exist (session scratchpad `compiler_array_loss_fix.diff`,
`dict_get_option_fix.diff`) and need a bootstrap + extended-smoke campaign;
until they land, code on the cranelift native lanes (`--backend cranelift
--mode dynload`, and the freestanding SimpleOS kernel build with
`SIMPLE_BOOTSTRAP=1`) must route data through safe channels.

## Channel table (evidence-backed)

| Channel | Verdict | Evidence |
|---|---|---|
| Scalar returns (i64/i32/u32/bool) | SAFE | scan-handoff scalar count survived while arrays died |
| text returns | SAFE | tag_name_of, accessors, theme ids all correct in guest |
| Runtime-builtin returns (`split`, `rt_text_to_bytes`) | SAFE | guest parsed 18 parts correctly while Simple-fn arrays died |
| Function-locals (incl. local arrays/aggregates) | SAFE | inlined parse_html scanner fixed the guest DOM |
| Self-mutation in `me` methods (`self.cache = ...`) | SAFE | glyph-cache conversion, verified by pixels |
| Field + array-element read on a receiver you hold | MOSTLY SAFE | `owner.active[0]` fixed draw_text; BUT see FontRenderBatch below |
| Plain aggregate returns | UNRELIABLE (layout-sensitive) | `aetheric_dark_theme_render_snapshot` works; `engine2d_font_owner_get_or_create` returned null in guest |
| Option-aggregate returns (`T?`, Some path) | BROKEN (deterministic) | instruction-proven: Some-check passes, payload masks to null (`_wm_draw_ir_window_revision`) |
| Tuple returns (`(i64, text)` etc.) | BROKEN | `cache_identity_snapshot` guest fault |
| Nested-array returns (`[[text]]`) | BROKEN | `_html_scan_events` → `nodes=1` |
| Array-typed module globals (even same-module) | BROKEN | `scan-handoff-loss returned=15 module=0` |
| Array FIELD of a struct crossing as return/param | BROKEN at scale | FontRenderBatch: scalars+atlas arrive, `quads=0` — persists even after staging to self fields (retest8), so treat any array-in-aggregate crossing as suspect |
| Chained method on an erased fn-return (`f().to_i32()`) | BROKEN | mis-dispatch into `Px.to_i32`, null receiver; bind a typed `val` first — and note rerun10: at some sites even the bound plain return is null |
| `.?` unwrap then field access | BROKEN (older class) | 2026-07-18 baremetal cr2=0x0 |
| `Dict.get` + `match case Some(x)` | BROKEN (deterministic, cross-lane) | probe 3 of `probes/cranelift_aggregate_return_min.spl`; fix drafted (match-decoder flat-lane) |

## Fix idioms (in preference order)

1. **Scalar/text projections in the owning module** — e.g.
   `active_wm_theme_id()`, `active_wm_theme_material_sha256()`,
   `cache_identity_generation()`. One accessor per needed field.
2. **Inline single-caller helpers** so arrays stay local (`parse_html`
   scanner, CSS `group_parts` helpers).
3. **Single-function restructure** — compute + consume in one function
   (`sha256_text`: bytes via builtin, K/w/hex all local).
4. **Sentinel plain returns instead of Option** — `FontRasterizer.invalid()`
   with `loaded_generation == 0`; callers test the scalar, never `!= nil`.
5. **One-slot list instead of an Option field** —
   `Engine2DFontOwner.active: [FontRenderer]` + scalar presence check.
6. **Presence check + plain slot read** for full-aggregate needs
   (`active_wm_theme_snapshot_present()` + `_unchecked()`); bind to a name
   that is NOT `snapshot` (freestanding lowering confuses same-named
   locals/methods).
7. **`mut` param threading** instead of returning the engine/aggregate
   (`_engine2d_draw_ir_render_commands(mut engine, ...)`).
8. **i64 code-point comparisons** — `char_code_at` yields plain i64; never
   chain `.to_i32()/.to_i64()` on it; compare code points (`== 103`), not
   1-char text handles.

## Attribution discipline (why the campaign converged)

- **Silent-on-healthy receipts at every conversion**: `scan-handoff-loss`,
  `[css-extract] degenerate`, `[web-material-fallback] digest-degenerate`,
  `[wm-content] material-sha-degenerate`, `[font-batch] degenerate`. A
  future regression names itself; verify each receipt with a
  negative control before trusting its silence.
- **Symbolize guest faults against the kernel ELF**: addresses are 8-hex
  (32-bit ELF); bracket `nm | sort | awk '$1 <= addr'`. For stripped host
  binaries: gdb SIGILL + frame-pointer walk + masked byte-matching against
  the symbol-bearing `native-cache/objects/` (reusable matcher:
  scratchpad `map_addrs.py`, 2026-07-26 session).
- **Verify build authenticity before interpreting any lane result**:
  parallel sessions sweep the shared working copy backwards (three
  occurrences on 2026-07-26 — twice rewinding landed fixes, once deleting
  a probe). Audit landed-marker presence (`grep` a distinctive literal per
  fix) in the WC before the run and in the binary/objects after; a
  reproduced crash at a "fixed" site usually means a stale build, not a
  regression.
- **The interpreter lane is only a non-regression check.** The cranelift
  lane is the oracle and is layout-sensitive: re-run it, never diff a
  single run.

## Current wall (2026-07-26 end state)

The hosted-WM text route still loses `FontRenderBatch.quads` after every
consumer-side idiom (including staging to self fields) — the remaining
loss is inside channels otherwise marked safe, at scale. Do not add more
call-site workarounds for it; the exit is the compiler campaign:
A1 (runtime-array identity for array-typed elements), B2 (loud diagnostic
for mutated array globals), and the Dict.get match-decoder fix — each
drafted, each requiring bootstrap + extended smoke per the stage-4
rollback precedent.
