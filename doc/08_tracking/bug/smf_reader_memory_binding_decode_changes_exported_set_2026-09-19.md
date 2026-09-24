# BUG: fixing `SmfReaderMemory.parse_binding` changes what `exported_symbols()` returns for a mixed-binding module

- **Filed:** 2026-09-19 (Fable review of lane A12, `doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md`)
- **Status:** OPEN — behaviour change is real and intentional (it is the
  correct decode), but it is a live risk surface, not fully closed
- **Severity:** Low today, Medium if unaddressed before any writer other than
  `80.driver/smf_writer.spl` starts emitting real `Local`-bound symbols
- **Component:** `src/compiler/70.backend/linker/_SmfReaderMemory/symbol_parser.spl`
  (`parse_binding`), consumed by `header_parser.spl`'s
  `SmfReaderMemory.exported_symbols()`, consumed live by
  `src/compiler/99.loader/module_loader_compat.spl` and by the thin
  `smf_reader.spl` shim (lane A12).

## Summary

Lane A12 fixed a real decode bug in `parse_binding`: `match b: 0: ... 1: ...
_: ...` on a raw `u8` never equality-matched a literal arm (same class of
defect as the one already fixed for `parse_symbol_binding` before A12, and
the same class later found in `parse_sym_type`/`derive_section_index` during
Fable review), so **every** symbol decoded as the default arm
(`SymbolBinding.Local`) regardless of its real binding byte.

That bug had a second-order effect nobody had noticed:
`SmfReaderMemory.exported_symbols()` (`header_parser.spl`) is written with a
non-vacuity fallback:

```
fn exported_symbols() -> [SmfSymbol]:
    ...
    for name in self.symbols.keys():
        val symbol = self.symbols[name]
        if symbol.binding == SymbolBinding.Global or symbol.binding == SymbolBinding.Weak:
            result.push(symbol)
    if result.len() == 0:
        for name in self.symbols.keys():
            if name != "":
                result.push(self.symbols[name])
    result
```

Before the fix, EVERY symbol decoded as `Local`, so the `Global`/`Weak`
filter loop above always matched zero, which unconditionally triggered the
fallback branch — `exported_symbols()` silently returned **every** symbol in
the module, `Local` ones included. After the fix, a real `Global`/`Weak`
symbol makes the filter loop non-empty, so the fallback never fires and
`Local` symbols are correctly excluded.

**Net effect:** for a module that legitimately mixes `Local` and
`Global`/`Weak` symbols, `exported_symbols()` used to (wrongly) include the
`Local` ones and now (correctly) excludes them. Any caller that resolves a
relocation by looking a symbol up through `exported_symbols()` — rather than
through `symbols_in_table_order()`, which is unaffected and always returns
every symbol regardless of binding — will now report a `Local` target as
"Unresolved symbol" (`module_loader_compat.spl`) where it previously
resolved by accident.

## Discriminating measurement

The reviewer's suggested probe (`test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl`,
base commit `9273a8f5679` vs A12 `355caf13ba3`) was run both ways on this
host (aarch64, `bin/release/aarch64-unknown-linux-gnu/simple` — no x86_64
`bin/simple` build is available here to run the x86_64-specific comparison
as literally requested). The result: **byte-identical** failing-test list
both before and after (17/18 failing, same 17 names) — that spec is already
red for unrelated reasons on this host, which mask the binding-decode
effect entirely. It is not a discriminating probe here.

A direct, decode-only measurement (bypassing that spec's unrelated failures)
does discriminate cleanly. Fixture: two symbols, `priv` (binding byte 0 /
`Local`) and `pub_fn` (binding byte 1 / `Global`), fed straight to
`SmfReaderMemory.exported_symbols()`:

| Symbol-parser state | `exported_symbols()` result |
|---|---|
| pre-A12 (`9273a8f5679`, buggy `parse_binding`) | `["priv", "pub_fn"]`, len=2, **both reported as `SymbolBinding::Local`** (the fallback path, not the filter) |
| post-A12 + Fable-review fixes (current) | `["pub_fn"]`, len=1, correctly excludes `priv` |

Measured directly against the two `symbol_parser.spl` revisions on this
host; not architecture-dependent (pure byte decode, no codegen involved), so
the aarch64-vs-x86_64 distinction the review asked about does not apply to
this mechanism — only the integration spec's unrelated aarch64-specific
failures made it look like it might.

## Why this is bounded today

`src/compiler/80.driver/smf_writer.spl:507`'s `build_symbol_entry` hardcodes
`binding: Global` (byte `1`) for every symbol it writes — there is currently
**no writer in this tree that ever emits a `Local`-bound symbol** in a real
SMF. `module_loader_compat.spl`'s relocation path in practice therefore never
resolves against a `Local` symbol found through `SmfReaderMemory` today. The
risk is latent, not active.

## What would need to happen for this to bite

Any writer path that starts emitting genuine `Local` bindings (e.g. a future
non-exported/static-symbol feature, or `LibSmfBuilder`/`lib_smf_writer.spl`
if they ever stop always forcing `Global`) will, for the first time, produce
modules where `exported_symbols()` and `symbols_in_table_order()` disagree in
a way that matters. Any consumer resolving names via `exported_symbols()`
(rather than the full ordered table) needs to be re-audited at that point.
`link.spl`'s `find_unresolved()` already uses the full `symbols` dict
(`SmfReaderImpl.symbols`, populated from `symbols_in_table_order()`), not
`exported_symbols()`, so it is not affected by this specific gap.

## Disposition

Not fixed here — this is a design question (should relocation resolution
ever consult `exported_symbols()` at all, given `symbols_in_table_order()`
already exists and is unaffected?) for whoever owns
`module_loader_compat.spl` / the loader relocation path, not an SMF-read-dedup
concern. Filed so the exported-set behaviour change introduced by the (still
correct) `parse_binding` fix is visible before a real `Local` symbol reaches
these paths.
