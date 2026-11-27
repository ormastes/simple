# Seed resolves enum variants by bare enum name; the last registered enum wins

- Status: open (worked around for `ByteOrder` by rename on work/codec-native-build-and-perf)
- Severity: P1 — breaks every `native-build` that imports `std.io_runtime`
- Found: 2026-10-19, lane work/codec-native-build-and-perf

## Symptom

```
error: semantic: unknown variant or method 'NotApplicable' on enum ByteOrder
```

Raised at `src/lib/nogc_sync_mut/io/text_session.spl:71`
(`utf8_text_session_codec`) by any program that loads `std.common.binary_io`
after `std.io_runtime`. `native-build` always does: the interpreted driver
(shb reader/writer, linker inspectors) imports `binary_io`.

Two-line interpreter reproducer:

```
use std.io_runtime.{file_write, file_read}
use std.common.binary_io.{ByteOrder}
```

## Cause

Two modules declared `enum ByteOrder` with different variants:
`std.common.encoding.external_text` (NotApplicable, LittleEndian, BigEndian)
and `std.common.binary_io` (LittleEndian, BigEndian, Native). The seed looks up
the enum by its bare name, not by owning module, and the last registration wins:

- interpreter: `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1375`
  (`enums` map keyed by name, `unknown_enum_variant_or_method`)
- MIR lowering: `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs`
  (`enum_declares_variant(enum_name, …)`) and `lowering_expr_call.rs:663`

The leak is also visible in string interpolation: a spec that never imported
`ByteOrder` interpolated `"{ByteOrder}"` to `<enum:ByteOrder>`.

## Workaround landed

The codec enum was renamed `TextByteOrder` (commit "fix(codec): rename external_text ByteOrder -> TextByteOrder"). Regression:
`test/03_system/compiler/text_byte_order_enum_collision_spec.spl` with fixture
`test/fixtures/native_text_byte_order_collision/main.spl`.

## Still open

Any duplicate enum name can hit this again. A live latent case:
`Encoding` is declared in `std.common.encoding.external_text` (Utf8, Utf16,
Unknown) and in `std.common.encoding.codec` (Utf8, Utf16LE, …). Loading
`codec` after `external_text` would break `Encoding.Utf16`.

## Fix direction

Key enum lookup by the owning module (the import binding in the caller's
environment), not the bare name, in both the interpreter and MIR lowering. Until
then, also check the pure-Simple compiler's enum tables for the same keying.

**Revalidated 2026-11-02: still plausible because open (worked around for ByteOrder by rename on work/codec-native-build-and-perf); no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 staged rollout, stage 1 (warning only)

Seed interpreter now emits `warning[enum-bare-name-ambiguous]` on stderr when an enum name is registered again with a different variant set (`warn_on_ambiguous_bare_enum_name`, evaluation_helpers.rs; hooked at GLOBAL_ENUMS/global_enums registration). No rejection yet; lookup is still last-wins. Unit tests: `cargo test -p simple-compiler --lib enum_bare_name_warning` (2 pass). Stage 2 (module-keyed lookup / hard error) still open.

## 2026-11-03 stage 2: current-module preference (fix-implemented-verification-pending)

Seed interpreter enum resolution now consults the enums declared by the CURRENTLY EXECUTING
module first (`module_cache::owner_module_enum`, keyed by `CURRENT_EXEC_MODULE` over
`MODULE_ENUMS_CACHE`), then the caller's `enums`, block-scoped and `GLOBAL_ENUMS` as before.
Applied at the 7 enum-name sites in `interpreter_method/mod.rs`, `interpreter/expr/calls.rs`
and `interpreter_call/mod.rs`. The `warning[enum-bare-name-ambiguous]` from stage 1 stays.
NOT yet verified: no seed build was possible (C: full, build refused under the 15 GB rule).
Repro: `bin/simple run test/fixtures/enum_bare_name_prefer_module/main.spl` against a seed
built from this commit; expect `alpha` / `gamma` (before: `unknown variant ... 'Alpha' on enum Mode`).
Residual: MIR lowering (`enum_declares_variant`, `type_registry.lookup(enum_name)`) is still bare-name keyed;
the module falls back to the interpreter via jit-fallback.

## 2026-11-03 status: fix-implemented-verification-pending (isl-seed-enum)

Stage 1 (7cd222d7585) and stage 2 (8c7d63e2c36) are on release/1.0.0; the
current-module preference sites are present in interpreter_method/mod.rs:1264,1319
and interpreter/expr/calls.rs:853,938. No seed build was possible (C: free < 15 GB),
so the fix is unverified. Row moved from open to fix-implemented-verification-pending.
Verify: build the seed, `simple run test/fixtures/enum_bare_name_prefer_module/main.spl`
(expect `alpha` / `gamma`), then `simple test test/03_system/compiler/text_byte_order_enum_collision_spec.spl`.
Residual: MIR lowering still bare-name keyed; sibling pure-Simple bug
enum_bare_name_collision_registry_2026-08-01 owned separately.

## 2026-11-11 addendum (lane seedfix, routed from lib3 / PR #8189): the JsValue co-load failure — FIXED, but the root was NOT the enum registry

Routed symptom: any compilation co-loading `std.js.engine.runtime` with a
`JsValue` import failed `method 'trim' not found on value of type enum in
nested call context` after the `enum-bare-name-ambiguous: JsValue` warning.

### The enum-registry diagnosis is disproven

A control repro with ZERO enum involvement fails identically on the refreshed
baseline seed (build-commit 0791c2b7f4a7):

```
fn main():
    val p = ["1+1"]
    val s = p.get(0).trim()   # error: method 'trim' not found on value of
    print s                   #   type enum in nested call context
```

`SIMPLE_DEBUG_NESTED_DISPATCH=1` shows the receiver was
`Option::Some("1+1")`. No imports, no enums — the `JsValue` ambiguous-name
warning seen in the routed repro is incidental: the runtime's own dependency
graph always loads both JsValue variant sets (common runtime re-export +
nogc/std types), so the warning fires on any runtime load and was spuriously
correlated with the failure.

### True root cause

The owner decision implemented 2026-11-09
(`array_get_contract_drift_crypto_2026-10-18`, status was
fix-implemented-verification-pending) changed the seed interpreter's array
`get`/`at` to return a BOXED `Option::Some(elem)`. The pure-Simple
interpreter's implementation of the same decision returns the FLAT encoding
(bare element in range, nil absent — see its `eval_array_read_method` and
`match_enum_variant_pattern`). The seed's boxed form broke every
`arr.get(i).<method>(...)` chain in the stdlib at the first non-fast-path use:
`js_parse_program_subset` does `parts.get(i).trim()` (nogc js engine
parser.spl:15), so ANY `JsRuntime.eval()` of a non-fast-path script died in
the parser — the js runtime was effectively unusable on the seed interpreter
since 2026-11-09.

### Fix (seed, restores pure-Simple parity; JIT/native lanes untouched)

- `interpreter_method/collections.rs` — array `get`/`at` return the flat
  encoding: bare element in range, `Value::Nil` otherwise (negative indices
  stay signed-checked, no saturation).
- `interpreter_patterns.rs` — the pattern matcher gains the flat Option arm
  the pure-Simple matcher has always had: a bare non-Nil, non-Enum value
  matches `Some(x)` (binding the value itself); Nil already matched `None`.
  This is the arm whose absence forced the boxed-Option choice in the first
  place ("This interpreter's pattern matcher rejects a bare i64 against
  Some(v)/None" — the 2026-11-09 comment).

Both halves are needed: flat returns without the matcher arm break
`if val Some(v) = arr.get(i)`; the arm without flat returns leaves the
chains broken.

### Verification

- Control repro (`["1+1"].get(0).trim()`): RED on baseline, GREEN on the
  seedfix seed (both engines).
- Routed repro (co-load `std.js.engine.runtime` + common `JsValue`, then
  `rt.eval("1+1")` / `'  hello  '.trim()`): RED on baseline, GREEN on the
  seedfix seed.
- `test/01_unit/lib/common/array_get_option_spec.spl` (the 2026-11-09 contract
  pin): GREEN on the seedfix seed — the flat encoding satisfies every
  Some/None/negative/nested row.
- New pin: `test/01_unit/lib/common/js_runtime_eval_coload_spec.spl`
  (co-load + parser-path evals + flat-contract rows).

### Residual (open, owner-level)

Full contract unification across lanes is still pending: on the JIT/native
lanes array `.get()` remains a typed Optional, so unwrapped chains there are a
compile-time error (per the gate doc's "reject unwrapped use with a precise
type diagnostic"). The stdlib's `.get()` chains only hold on flat-encoding
lanes; a systematic `[i]`-ification of the js engine (507 `.get(` sites in
nogc alone) or a lane-uniform contract revisit remains open. The enum
bare-name collision itself (this doc's original subject) also remains open —
stage 2 covers the interpreter's 7 sites; MIR lowering is still bare-name
keyed.
