# `vhdl_design_catalog_spec.spl` — `cannot cast dict to i64` (interpreter-incompatible raw-pointer cast)

- **Date:** 2026-07-30
- **Lane:** VHDL1 (mission-critical hardening campaign)
- **Status:** Root cause fixed for the cast defect. A second, separate, pre-existing bug was
  uncovered underneath it and is left OPEN (see "Follow-on defect" below) — not fixed here.

## Background / attribution

Lane DEAD1, while auditing newly-live `SymbolKind` match arms, observed this spec at 20/21
failing and explicitly declined to attribute it to their own PTR1/PTR2 work, recording it as an
open, unattributed item in
`doc/08_tracking/bug/newly_live_symbolkind_arms_audit_2026-07-30.md` ("Observed test regression"
section). This doc is the follow-up diagnosis DEAD1 asked for.

DEAD1 also flagged that the file carries uncommitted WIP from another session. Confirmed still
true at investigation time: `git diff origin/main -- .../vhdl_design_catalog.spl` (before my
edit) showed exactly 3 cosmetic match-arm-binding renames around lines 105–185
(`FuncPtr(signature)`→`FuncPtr(inner_sig)`, `Call(dest, func, args)`→`Call(dest, callee, args)`,
`CallTerminator(..., func, ...)`→`CallTerminator(..., callee, ...)`), nothing else. My fix (below,
at lines 18 and 82–86) does not touch or overlap those lines — verified by re-diffing after the
edit.

## Repro

```
env -u SIMPLE_TIMEOUT_SECONDS timeout 400 bin/simple test --no-session-daemon \
  test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl
```

**Before fix:**
```
Results: 21 total, 1 passed, 20 failed
```
All 20 failures: `semantic: type mismatch: cannot cast dict to i64` (no file:line surfaced by the
runner itself — root-caused by source inspection below).

## Root cause

`src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl:83` (pre-fix):

```simple
fn vhdl_catalog_symbol(symbol: SymbolId, rebase: Dict<i64, i64>) -> SymbolId:
    val mapped = rt_dict_get_i64_raw(rebase as i64, symbol.id)
    SymbolId(id: if mapped == 0: -1 else: mapped >> 3)
```

`rebase as i64` casts a `Dict<i64,i64>` handle directly to an `i64`, on the assumption that under
native codegen a `Dict` lowers to a raw pointer that can be reinterpreted as an integer and handed
to the raw extern `rt_dict_get_i64_raw(dict: i64, key: i64) -> i64`, whose result is a still-boxed
tagged word (hence `>> 3` to strip the 3-bit tag, `0` as the nil-boxing sentinel for "not found").
This is a deliberate low-level workaround for the documented **native-only** `Dict.get()`
corruption family (`doc/07_guide/language/dict_native_pitfalls.md`).

**Mechanism:** `bin/simple test` hard-defaults to the tree-walk interpreter (not native codegen,
not JIT — see `.claude/rules/testing.md`). The interpreter's cast evaluator
(`src/compiler_rust/compiler/src/interpreter/expr/casting.rs`, function `cast_to_numeric`,
~lines 116–149) has **no match arm for `Value::Dict`** — grepped the whole 227-line file, zero
hits for `Dict`. Every `Dict as <numeric>` cast falls to the `_` arm and returns exactly
`type mismatch: cannot cast {val.type_name()} to {target.name()}` → `"dict"` / `"i64"`. This is
not new/regressed code; `Value::Dict` has never been handled there. Per the same guide doc (line
4): "[the native Dict bugs] are native-only — the interpreter and the Rust seed both behave
correctly" — i.e. the interpreter never had the corruption this cast works around, so the
workaround itself is the only thing broken here, and only under the interpreter.

`vhdl_catalog_symbol` is called from nearly every function in the catalog-building pipeline
(`vhdl_catalog_function`, `vhdl_catalog_type`, `vhdl_catalog_operand`, etc. — all of them rebase
`SymbolId`s through this one helper), so the failure was universal across the spec file. The one
test that passed before the fix (`"selects the VHDL root only from explicit compile inputs..."`)
never calls into the catalog builder at all — it only reads and greps a source file's text.

**When it broke:** `rt_dict_get_i64_raw(rebase as i64, ...)` has been in this file since
2026-07-24 (first `git log -S` hit for that string in this file's history). `Value::Dict` has
never had a cast arm in the Rust interpreter. So this has been broken under `bin/simple test`
since 07-24 — it predates today's SymbolKind audit and is unrelated to DEAD1's PTR1/PTR2 landing.
No mechanistic link to the flagged `Struct | Enum` match arms was found (confirmed: those arms
populate the `rebase` dict's *contents*, not the cast expression that fails).

## Fix applied

Replaced the raw-pointer/native-workaround pattern with the officially documented
engine-portable-safe pattern from `doc/07_guide/language/dict_native_pitfalls.md`
(`contains_key(k)` + indexed read `d[k]`), which is correct on both the interpreter and native
codegen:

```simple
fn vhdl_catalog_symbol(symbol: SymbolId, rebase: Dict<i64, i64>) -> SymbolId:
    if rebase.contains_key(symbol.id):
        SymbolId(id: rebase[symbol.id])
    else:
        SymbolId(id: -1)
```

Also removed the now-unused `extern fn rt_dict_get_i64_raw(dict: i64, key: i64) -> i64`
declaration (line 18) — dead code per repo code-style rules, no other call site in this file.

Files modified:
- `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` (lines 18, 82–86 only; isolated
  from the other session's WIP renames at lines 105–185)

## Result after fix

```
Results: 21 total, 7 passed, 14 failed
```

The `cannot cast dict to i64` error is gone from all 21 cases. 1 → 7 passed.

## Follow-on defect uncovered (OPEN, separate, NOT fixed here)

The 14 remaining failures are a **different** bug, unmasked once the cast crash stopped hiding it.
New errors: `semantic: undefined field 'has_vhdl_metadata': cannot access field on value of type
'nil'`, and (mostly) `VHDL design catalog found no @hardware entry in selected root module(s)`.

Root cause: `vhdl_catalog_function` (`vhdl_design_catalog.spl:212`, pre-existing, unchanged by my
fix) unconditionally discards the input `MirFunction`'s hardware-entity attribute when rebasing:

```simple
has_vhdl_metadata: false, vhdl_metadata: vhdl_hardware_metadata_default(),
```

It is restored only if the driver-source hardware-metadata sidecar (`hardware_metadata_rows`)
contains a matching row (`vhdl_design_catalog.spl:740`, `func.has_vhdl_metadata = true`). Every
`it` block in this spec that builds a `MirFunction` with `has_vhdl_metadata: true` directly (via
the test helper `catalog_function(...)`) and calls the **non-sidecar** entry points
(`vhdl_build_design_catalog` / `vhdl_build_design_catalog_with_hir`, which pass no matching rows)
therefore always loses the flag and always reports "no @hardware entry" — for every function in
the design, not just the test's target function.

- **Introduced by:** commit `8eac72ffb5bb` "wip(vhdl): preserve catalog provenance across
  self-hosting", 2026-07-24 (`git blame` on both lines) — a WIP commit, predates today's audit,
  **not** caused by DEAD1's PTR1/PTR2 SymbolKind work.
- **Not fixed here:** whether the direct MIR `has_vhdl_metadata` attribute is *intentionally*
  deprecated in favor of sidecar-only hardware detection (an architecture decision, in which case
  the spec's non-sidecar test cases are the ones that need updating) or whether the reset is a bug
  that should preserve the original flag when no sidecar row overrides it, is not something I can
  determine confidently without input from whoever owns the hardware-metadata-sidecar feature
  (REQ referenced in the spec: "recovers hardware metadata from the driver source sidecar"). Per
  the "fix only if minimal and unambiguous" rule, this is neither, so it is left open. Flagging for
  the orchestrator / file owner rather than guessing.

## A/B interpreter vs JIT

Not applicable here: the failure is a deterministic semantic-analysis rejection of an explicit
`as i64` cast in code shared by the interpreter (not codegen-specific), and `bin/simple test`
only ever runs specs through the interpreter — there is no JIT code path for `describe`/`it` specs
to A/B against.
