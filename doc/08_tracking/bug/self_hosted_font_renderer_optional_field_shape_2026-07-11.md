# Self-hosted semantic resolver drops `FontRenderer.ttf_rasterizer`

Date: 2026-07-11
Status: Open
Severity: P1 — blocks Simple 2D vector-font integration

## Reproducer

```text
bin/simple test test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl --mode=interpreter
semantic: class `FontRenderer` has no field named `ttf_rasterizer`
```

The field is declared in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` as `ttf_rasterizer: FontRasterizer?`; constructors and existing methods reference it. The same field existed before this lane and the focused suite previously reached runtime loading, so this is a resolved-class-shape regression triggered by the extended owner/cache shape rather than a missing declaration.

## Attempts (bounded)

1. Expanded compact assignment syntax after the parser rejected assignment-bodied one-line forms.
2. Put every constructor named field on its own line.
3. Restored the optional custom-class field as the final class field.

All three post-fix executions still report the identical missing-field semantic error. Logs:

- `build/simple-2d-vector-fonts/system_spec_postfix.log`
- `build/simple-2d-vector-fonts/system_spec_postfix_2.log`
- `build/simple-2d-vector-fonts/system_spec_postfix_3.log`

## Required Next Investigation

Reduce the class/import cycle (`font_renderer` <-> `font_rasterizer`) against the self-hosted class-shape builder and compare the resolved field table before/after adding `FontCacheStats`/generation fields. Fix the owner semantic path once; do not replace the typed optional field with raw handles, module globals, or a feature-local runtime alias.
# 2026-07-11 follow-up

The import-cycle/class-shape failure is resolved by extracting shared types to
`font_types.spl` and lazily constructing the Engine2D renderer. Both native and
interpreter compilation now reach the scenarios.

The remaining blocker is runtime state propagation: `Engine2D.load_font()`
returns true, and the freshly rebuilt `libspl_fonts.so` directly reports a valid
face, `has_glyph('A') == 1`, and three positioned glyphs for `"A A"`. However,
the public Engine2D path still produces zero pixels and zero cache hits; bitmap
rendering after `unload_font()` is also suppressed in this system-spec process.
This strongly points at the module-global optional `FontRenderer` value being
copied or not retaining mutation across `_engine2d_fonts()` returns, rather than
a font parser or ABI failure.

The native scenario consumed the mandatory three verify/fix cycles. Continue in
a fresh scoped session with a reference-stable owner (for example an Engine2D
field or a boxed/shared renderer) and a one-assert state-retention probe before
re-running the full system spec.

---

## Re-investigation 2026-08-17 (worker W7)

Binary for every number below: `bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed). No bootstrap was run.

**Both filed symptoms are addressed in `src/lib/`; the compiler defect under
them is not.**

1. `semantic: class FontRenderer has no field named ttf_rasterizer` — resolved
   by the `font_types.spl` extraction recorded in the 2026-07-11 follow-up. The
   field is declared at `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:785`
   and referenced by all three constructors; the error does not reproduce.
2. "module-global optional `FontRenderer` copied / not retaining mutation" — the
   real mechanism was found on 2026-07-30 and is documented in-file at
   `font_renderer.spl:338-351`: a module-global `[FontRenderer]` cache whose
   nested `ttf_rasterizer: FontRasterizer? -> selected_blob: [u8]` did not
   survive store/read-back (has_ttf=0 on 74/74 cache hits). The cache was
   FLATTENED to scalars as a call-site workaround. See
   `font_renderer_cache_nested_aggregate_loss_2026-07-27.md`.

### The requested one-assert state-retention probe — reduced and reproduced

16 lines, no fonts, no SFFI, no Engine2D: `Outer { name: text, inner: Inner? }`
with `Inner { blob: [u8] }`, stored in a module-global `[Outer]` and read back.

| engine | result |
|---|---|
| interpreter | `name=a` / `blob_len=3` — correct |
| jit | `name=a`, then `runtime error: invalid field receiver` + **core dump** |

The flat scalar survives; the optional nested aggregate faults outright — worse
than the silent degradation originally measured. Invisible to the suite because
`bin/simple test` is the tree-walk interpreter.

### Fence shipped

- `test/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.spl`
  (+ `_optional_aggregate_jit_probe.spl`): `Results: 4 total, 3 passed, 1 failed`
  — the one failure is precisely the nested-blob read-back; the flat-scalar and
  interpreter-reference assertions pass, so the RED cannot be misread as a
  general breakage.

**Unblock condition:** fix the aggregate field receiver on the Cranelift lane in
`src/compiler_rust/**`. Outside this lane's ownership — **BLOCKED-CROSS-OWNER**.
Do NOT re-nest a FontRenderer into a module-global array until this spec is green.

### Family note

Same *detection* family as
`stage4_selfhost_sha3_hir_infer_and_stubs_2026-06-28.md`: a value-shape defect
that exists only under the JIT and is structurally unreachable from the
interpreter-only spec suite. Different mechanisms (61-bit int boxing there,
aggregate field receiver here), one shared blind spot.
