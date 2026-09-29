# LayoutGlyph struct-in-array i64 fields read back tag-shifted on the freestanding native lane — zero glyph quads, no text on SimpleOS desktop

- **ID:** layoutglyph_struct_array_i64_field_tag_shift_readback_2026-07-20
- **Status:** ROOT-FIXED on the hosted native-build path (x86_64-unknown-linux-gnu, self-hosted `src/compiler/50.mir` MIR lowering + `src/compiler_rust` seed driver); the per-site scalar-mirror workaround in `_prepare_text_active` is now redundant but was left in place (out of scope for this change — see Root-fix note below); freestanding/OVMF x86_64-unknown-none NOT independently re-verified in this change (same target-independent MIR lowering code path, so expected to carry over, but the SimpleOS desktop boot/OVMF gate was not re-run — flag for a follow-up board-runnable check per `.claude/rules/board-runnable.md`)
- **Severity:** P1 — silently killed ALL glyph text on the SimpleOS x86_64 desktop (taskbar clock, window titles, taskbar labels); no crash, no diagnostic
- **Lane:** native-build (Rust seed frontend, cranelift, `--entry-closure`, x86_64-unknown-none), OVMF/GRUB multiboot boot
- **Class:** the documented "BoxInt <<3 / tag-shifted views of one boxed integer" codegen family (see GLYPH-FIX-3 retraction note in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` and `baremetal_option_field_unwrap_faults_class_2026-07-18.md` for siblings)

## Symptom

At origin/main tip (base 9fdeaee2314, 2026-07-20) the SimpleOS desktop
(`gui_entry_desktop.spl`) boots to `desktop-ready` with a 99.83%-coverage
frame but renders ZERO glyph ink anywhere: no window title, no taskbar
labels, no taskbar clock (`clock_region_ink_pixels=0`, kernel logs
`[font-evidence-unavailable] reason=canonical-taskbar-clock-oracle-pending`).
The aqua-glyph OVMF gate honestly fails on the clock-ink oracle.

## Probe evidence (gated boot probes, OVMF boot, 2026-07-20)

The glyph pipeline is healthy right up to the quad producer:

```
[e2d-text-probe]  ir kind=plain len=11                                # draw-ir text cmd, text present
[vec-text-probe]  draw_text-entry text_len=11 has_sffi_ttf=1          # engine entry, text present
[vec-glyph-probe] prepare-entry content_len=11 font_size=12           # renderer entry, text present
[vec-glyph-probe] gwc-pre-insert cp=83 w=5 h=12 adv=6 plen=60         # rasterizer: REAL glyph bitmap
[vec-glyph-probe] active-after-layout_text layout_len=0 ...           # rast.layout_text: empty -> fallback loop
```

The fallback loop pushes correct values into `layout: [LayoutGlyph]`
(cp=83 'S', w=5 h=12). Reading the SAME entry back in the quad loop:

```
[vec-glyph-probe] quadloop-after-reget i=0 cp=0 w=0 h=0 face_id=0 face_gen=0 glyph_index=2305843009213693951
[vec-atlas-probe] producer-empty n_quads=0 overflow=0 content_len=11
```

- `cp=0` — the pushed `codepoint.to_i64()` (83) reads back as the `&7`
  tag-view (83<<3=664; 664&7=0), the exact three-shifted-views signature
  documented in the GLYPH-FIX-3 note.
- `glyph_index=2305843009213693951` (0x1FFFFFFFFFFFFFFF) — nil sentinel.
- Every draw therefore produces `n_quads=0` (with `valid=true`, since the
  batch construction itself succeeds), `_draw_font_batch_plan` "succeeds"
  with nothing to blit, and the draw-ir layer counts the command as
  rendered — a silent no-op.

## Regression window

The GLYPH-FIX campaign (2026-07-19) had this exact path producing
`n_quads=1..13` with real atlas coverage (see
`font_render_batch_transform_identity_default_not_applied_2026-07-19.md`
Evidence section) — the LayoutGlyph round-trip worked then. At tip it is
corrupt. Prime suspect (UNVERIFIED — not bisected): `f33dc52320f`
"fix(runtime): heap-box f64 on the native-build path (lossless container
floats)" changed container value boxing in the same window. A bisect boot
of `gui_entry_desktop` at `f33dc52320f^` vs `f33dc52320f` would confirm.

## Per-site workaround (landed with this doc)

`_prepare_text_active` (`font_renderer.spl`): scalar mirror arrays
(`fallback_cps: [i32]`, `fallback_xs: [i64]`) are filled alongside the
fallback `layout.push(LayoutGlyph(...))` and preferred over re-reading the
LayoutGlyph fields in the quad loop. Scalar primitive arrays round-trip
correctly on this lane (long-proven by e.g. the PMM refcount `[u16]`).
`FontRenderQuad`-in-array reads back correctly (consumer probes show real
`first_w/first_h/first_cov_nz`), so only the LayoutGlyph hop needed the
mirror.

**Also affected, NOT yet fixed:** `render_text_payload`
(`font_renderer.spl:~897`) has the identical fallback-then-reread pattern
and presumably the same corruption; it is not on the taskbar-clock path
and was left unchanged to keep this change minimal.

## Residual after the workaround (separate, smaller defect)

With quads restored, the desktop renders the taskbar clock digits
("00:00", 328 ink pixels in the clock crop vs 312 in the Jul-19 canonical)
and most label text, but SOME codepoints render as the 8x16 notdef box
(observed: 'H'/'W' in "Hello World", 'm' in "Terminal") — i.e. specific
re-get lookups return the notdef glyph instead of the cached real glyph.
Suspected: the glyph CACHE entry round-trip (another struct-in-container
hop; `gwc-entry ... cache_rcfg_id_len=0` also shows the cache's
render-config identity string reads empty) — same codegen family. Not
chased further in this change; the taskbar-clock oracle (digits) renders
correctly and deterministically.

## Root-fix direction

Fix the tag-shift on i64 struct-field round-trips through arrays in the
freestanding native codegen (boxing owner), then delete the scalar
mirrors. Bisect `f33dc52320f` first.

## Root-fix (2026-07-20, root-fix lane)

**Bisect verdict on `f33dc52320f`: NOT the cause.** That commit only touches
the `MirTypeKind.F64`/`F32` arms of `box_runtime_value`/`decode_runtime_value`
(expr_dispatch.spl); `LayoutGlyph`'s six fields are all `i64`, whose box/unbox
(`<<3`/`>>3`) arms are untouched by that diff. No bisect build was needed to
confirm this — the diff itself has no code path that a plain-i64 struct field
could reach. Full-diff review only; not literally checked out at the parent
SHA (not worth a second seed rebuild once the actual mechanism below was
isolated empirically).

**Reproduced (hosted native-build, x86_64-unknown-linux-gnu, NOT the
freestanding OVMF/x86_64-unknown-none lane the original symptom was seen on
— see Status line):** a class with i64 fields pushed into an array declared
via an *initially-empty* `[]` literal reproduces exactly. This is the *precise
shape* `spl_fonts.spl` uses:

```
src/lib/nogc_sync_mut/sffi/spl_fonts.spl:542   var glyphs: [LayoutGlyph] = []
src/lib/nogc_sync_mut/sffi/spl_fonts.spl:545       glyphs.push(LayoutGlyph(...))
```

Minimal repro (`class Rec` with the same 6 i64 fields as `LayoutGlyph`):
```
var arr: [Rec] = []
arr.push(Rec(codepoint: 83, ...))
arr[0].codepoint   # BEFORE FIX: SIGSEGV on the hosted native-build lane
```
An array *literal* with elements (`[Rec(...), Rec(...)]`, or a struct in a
`Dict<text, Rec>`, or a bare local struct) was **not** affected — isolating
the defect to the empty-literal + `.push()` combination specifically.

Symptom differs by lane: on the freestanding/OVMF lane the doc's own probe
observed a *silent wrong value* (`cp=0`, no crash — the shredded pointer bits
happened to fall in mapped memory or get read as a plain integer downstream).
On the hosted Linux lane the same shredded-pointer mechanism instead
**SIGSEGVs** on the very next field access, because `emit_get_field` derefs
the corrupted "pointer" immediately. Same root cause, different observable
surface depending on what garbage address the `>>3` shift produces on each
target/allocator. The link to this doc is the *code pattern* (confirmed
identical to `spl_fonts.spl:542/545`), not a byte-identical repro of the
doc's captured symptom.

**Root cause** — `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
`box_runtime_value`/`decode_runtime_value` (~line 307/395), fed by
`array_element_struct_syms` (`src/compiler/50.mir/mir_lowering_types.spl:192`):

- `lower_array_lit` (`method_calls_literals.spl:2640`) captures a struct
  element's name from `struct_value_syms` into
  `array_element_struct_syms[array_local.id]` — but only when the array is
  built as a literal with elements present at construction time.
- The `.push()` handler (`method_calls_literals.spl:2373`, "Bug #149") and the
  `arr[i] = value` handler (`mir_lowering_stmts.spl:1021`) both call
  `note_container_elem_type(container, value_local)` before boxing the pushed
  value, but that helper (`expr_dispatch.spl:388`, pre-fix) only recorded
  `runtime_elem_value_type` for `F64`/`F32` values (the sibling f64 fix's own
  addition) — it never touched `array_element_struct_syms` for `Struct`-typed
  values.
- Net effect: for `var glyphs: [LayoutGlyph] = []` + `.push(...)`,
  `array_element_struct_syms` is **never populated** for `glyphs`. The later
  read (`expr_dispatch.spl`'s `Index` case, ~line 1945, and the `for`-loop
  desugar in `mir_lowering_stmts.spl`, ~line 1747) both gate a correct
  no-op `Opaque(struct_name)` decode on `array_element_struct_syms` having a
  "real" name; without it they fall through to `decode_runtime_value`'s
  `is_integer` default (`raw >> 3`, `expr_dispatch.spl:400`), shredding the
  struct's heap pointer.
- On the *push* (write) side this is harmless by itself —
  `box_runtime_value`'s match has no arm for `MirTypeKind.Struct`, so it
  falls through to `case _: local` (no shift) — the corruption is entirely a
  **read-side type-tracking gap**, not a write-side boxing bug.

**Fix** (`expr_dispatch.spl`, `note_container_elem_type`): mirror
`lower_array_lit`'s capture — look up `struct_value_syms.get(value_local.id)`
for the value being pushed/assigned, and if it names a real struct, record it
into `array_element_struct_syms[container.id]`, exactly like the literal-array
path already does. This is target-independent MIR lowering (no
freestanding-vs-hosted branch), so it should apply to both native-build
targets; only the hosted x86_64-unknown-linux-gnu lane was re-verified here.

**Verified round-trips (hosted native-build, before/after)**: bare struct
local (unaffected either way); array literal (unaffected either way); array
built via empty-`[]` + `.push()` — **SIGSEGV before, correct values after**
— positive (83), zero (0), negative (-7), and a value at the tag boundary
(2^60-1 = 1152921504606846975); `for`-in over the same push-built array
(separate decode call site, also fixed); struct value in a
`Dict<text, Rec>` (unaffected either way — dict value/key typing doesn't
route through `array_element_struct_syms`).

**Regression guards added:**
- `test/03_system/native/struct_array_push_i64_field_tagshift.spl` — the
  repo's established convention for native-build-only regressions (checked
  by exit code via `native-build --entry`, per
  `test/03_system/native/README.md`); expected rc **30**; before the fix,
  crashes (SIGSEGV, rc 139).
- `test/01_unit/compiler/codegen/struct_array_i64_field_precision_spec.spl`
  — SSpec parity guard. **Not run to a `Passed:`/`Failed:` verdict block in
  this change**: `bin/simple test` needs the self-hosted binary; only the
  Rust seed was available/built in this lane, and the seed's `test`
  subcommand re-interprets the entire compiler+stdlib from source to stand
  up the test runner, which did not complete within this session's time
  budget across three attempts (>120s each, never reached executing the
  spec). This spec also runs on the *interpreter* evaluator, which already
  round-tripped these values correctly before this fix (confirmed via
  `bin/simple run` on an equivalent probe) — the native-build return-code
  file above is the real regression gate for this bug; the SSpec file
  documents/guards evaluator parity for whoever next has a self-hosted
  binary handy.

**Not in scope / not re-verified:** the freestanding x86_64-unknown-none
OVMF/SimpleOS desktop boot (per the Status line); `render_text_payload`'s
identical pre-existing fallback-then-reread pattern (already flagged above as
not-yet-fixed and left unchanged); the glyph-cache residual defect described
above (separate struct-in-container hop, not this bug). Deleting the
`_prepare_text_active` scalar-mirror workaround now that the root cause is
fixed is left to whoever next touches `font_renderer.spl` with board access
to re-verify the OVMF gate, per this repo's board-runnable rule.
