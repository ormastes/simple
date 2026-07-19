# CLASS: Option-unwrap / if-val field access faults on baremetal native codegen

**Date:** 2026-07-18
**Status:** Per-site workarounds LANDED across the font lane (SHAs below). **Root
compiler codegen bug is OPEN** — it has only been worked around at each call
site, never fixed in the codegen owner. This file exists to track the *class*,
not to claim it is fixed.
**Severity:** P1 — silent runtime fault (cr2=0x0) with no diagnostic; each
occurrence produces a recoverable-fault storm that can exhaust the baremetal
heap.
**Component:** compiler codegen (freestanding `--entry-closure --backend
cranelift --target x86_64-unknown-none`), Option/box-unbox + Option-binding
lowering.

## Symptom

On the freestanding SimpleOS kernel build, unwrapping an `Option`/nilable value
and then reading a field on the unwrapped value — the `candidate.?.local_path`
shape, and the `if val x = opt: ... x.field` shape — faults at runtime with
`cr2=0x0` (nil-deref). The same source runs correctly hosted (interpreter and
hosted JIT), so it is a baremetal/freestanding codegen defect, not a source
logic error. Because the kernel's fault-recovery stub advances RIP by a fixed 2
bytes and retries, each faulting text draw produces a fault storm (tens of
thousands of recovered faults) that ends in heap exhaustion.

## Root (shared)

Option-unwrap-then-field-access and `if val` binding miscompile on the
baremetal native lane. Confirmed from the workaround diffs:

- `a4750208a5c` — `val candidate = selected.?` then a field/interpolation on the
  unwrapped Option-derived receiver faults; replaced with a `match`/typed
  intermediate.
- `567fbf3eaaf` / `5c4dbfc1922` — `candidate.?.local_path` faults; replaced with
  a path-based free helper (`selected_font_asset_local_path_for_identity`) that
  reads `.local_path` off a **direct array-element struct** (kernel-proven safe)
  inside a `while` loop, never off an unwrapped Option.
- `46149d4306d` — typed intermediates + `match`-based Option checks on the
  first-executed rasterizer path.
- `e02879c8eae` — `if val` binding faults **downstream** (the hit path returns
  nil / a corrupt value); replaced with `match`-based Option unwraps in the
  selected-outline rasterizer.
- `cd411c080a4` — same `match`-unwrap workaround applied in `sfnt_glyf` while
  flattening the cross-module glyph rasterization API.

The common fix pattern at every site is identical: **avoid the language-level
Option unwrap/`if val` binding and hand-roll a `match` or a direct
array-element/while-loop access.** That this same mechanical rewrite is needed
at five+ independent sites is the signature of one underlying codegen bug, not
five font bugs.

## Fixing commits (per-site workarounds — NOT a root fix)

- `567fbf3eaaf` fix(os/font): registered-identity load via path helper
- `5c4dbfc1922` fix(os/font): register path uses path-based identity
- `a4750208a5c` fix(os/font): compute rasterizer identity inside font_registry
- `46149d4306d` fix(os/font): typed intermediates + match-based Option checks
- `e02879c8eae` fix(os/font): match-based Option unwraps in selected-outline rasterizer
- `cd411c080a4` fix(os/font): flat cross-module glyph rasterization API + match unwraps in sfnt_glyf

## Affected files (workaround sites)

- `src/lib/common/encoding/font_registry.spl`
- `src/lib/common/encoding/sfnt_glyf.spl`
- `src/lib/common/encoding/sfnt.spl`
- `src/lib/nogc_sync_mut/sffi/spl_fonts.spl`
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`

## This is a recurring class — needs a ROOT fix, not more workarounds

Per the standing directive `feedback_recurring_problem_team_analysis_and_tests`
(when a bug class recurs, team-analyze the root and add regression tests around
the logic, not just patch the instance), this class needs:

- **(a) a compiler root-cause fix in the codegen owner** — the Option
  box/unbox + Option-binding (`if val`) lowering on the freestanding/cranelift
  path — so the language-level `opt.?`-then-field and `if val x = opt:` shapes
  compile correctly on baremetal and the ~5 per-site match rewrites above can be
  reverted. Likely locus: `src/compiler_rust/compiler/src/mir/lower/` and
  `src/compiler_rust/compiler/src/codegen/` (box/unbox + Option-binding
  lowering).
- **(b) regression tests around the box/unbox + Option-binding logic**, run on
  the freestanding cranelift AOT config (not just hosted JIT), covering:
  unwrap-then-field-access (`opt.?` then `.field`), `if val x = opt:` hit-path
  value integrity, and `match`-vs-`if val` parity — each asserted to produce the
  same result hosted and freestanding.

## Related / cross-references

- `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md` — the
  comprehensive freestanding-codegen defect log. **C2** ("`if val x = opt:`
  binding returns nil on the hit path") is the closest documented mechanism to
  this class; C2's note that `.?` is the existence predicate (`rt_is_some` ->
  bool) is exactly why the `opt.?`-then-field unwrap shape is fragile on this
  path. This class file is the font-lane index into that pattern.
- Documented Option-handling family (same underlying pattern on other lanes —
  evidence the class needs a root fix, not another workaround):
  `interp_if_val_option_binding_enters_body_on_nil_2026-07-02.md`,
  `interpreter_ifval_optioncheck_return_divergence_2026-07-17.md`,
  `seed_interp_option_match_falls_through_at_scale_2026-07-18.md`,
  `native_text_option_unwrap_pointer_value_2026-07-15.md`,
  `native_try_op_on_option_silent_wrong_2026-07-14.md`,
  `interp_u64_high_bit_option_unwrap_corruption_2026-07-11.md`,
  `free_fn_optional_wrap_2026-06-26.md`.
- Related but distinct compiler workaround:
  `fontrenderconfig_entry_closure_receiver_binding_miscompile_2026-07-18.md`
  (method receiver-binding, not Option unwrap).
