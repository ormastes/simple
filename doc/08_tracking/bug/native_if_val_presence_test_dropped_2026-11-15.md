# Native `if val` takes the Some branch on None (presence test dropped)

- **Found:** 2026-11-15 (Stage 2 cranelift + llvm, release tip)
- **Status:** fixed in MIR source; native confirmation pending a Stage 2 built from the fix
- **Class:** `doc/07_guide/compiler/robustness/stage2_native_miscompile_classes.md` row 20

## Symptom

Natively built programs run the body of `if val x = <T?>` when the value is
None, with `x` bound to the runtime nil word `3`. `while val x = next()` never
terminates. `if val r = res.ok` on an `Err` binds `3`. The seed interpreter is
correct. Oracle: `test/fixtures/native_if_val_presence/main.spl` (header = seed
stdout). Pre-fix Stage 2 (`bootstrap-fable-34`, 43d59a39947), identical on
cranelift and llvm:

| row | seed | native (pre-fix) |
|---|---|---|
| `call_int 0`, `local 0`, `param 0`, `field 0`, `elif 0`, `try 0`, `param lit-none` | `none` | `some 3` |
| `nested 2 0` / `nested 0 2` | `outer 3` / `none` | `both 3 3` / `both 3 3` |
| `ok f` (`.ok` on Err) | `none` | `some 3` |
| `dict b` / `dict c` / `dict d` (values 3, 16, -8) | `some 3/16/-8` | `none` / `some 2` / `some -1` |
| `index 1..3` (`[i64?]` element) | `some 0/3/-7` | handle bits |
| `err f` (`.err` text payload) | `some bad` | an integer |
| `while` | `seen 2,1,0,` | never ends (timeout) |

`call_text`, `call_bool`, `call_float`, `call_arr`, `call_point`, `match`, `.?`
truthiness, `??` and `?` were already correct.

## Root cause

`if val x = e` is parser-desugared (`10.frontend/_FlatAstBridge/convert_nodes.spl:2136`)
to `val x = e.?` plus `x != nil`. The ExistsCheck (`.?`) lowering
(`50.mir/_MirLoweringExpr/expr_dispatch.spl`, `case ExistsCheck`) does emit
`rt_is_some` on the subject and yields a payload-or-nil WORD. The binder is
typed by the PAYLOAD (`20.hir/hir_lowering/statements.spl:101`), so for an
`i64?` subject `x` is a plain `i64`. The nil-compare in the Binary lowering
(`expr_dispatch.spl`, the `nil_compare_operand_is_plain_scalar` fold, ~5170)
treats a statically non-optional scalar as never-nil and folds `x != nil` to
`true`. Only Float/Bool payloads were exempted (`exists_scalar_word_locals`).
`.ok`/`.err` (`lower_result_unwrap_core`) produce the same payload-typed word,
and the `.?` on them returns the base unchanged (plain scalar early return).

It is NOT the `SIMPLE_BOOTSTRAP=1` return-type erasure: the same fold appears
with ordinary HIR lowering.

Removing the fold is not a fix: a present 3 and the nil word are the same bits,
so `x != 3` would turn every `Some(3)` into None. The presence must come from
the producer.

## Fix

`MirLowering.presence_word_locals` maps a payload-or-nil word to the Bool local
that proves it present:

- ExistsCheck records its `rt_is_some` result for its word.
- `lower_result_unwrap_core` with a nil fallback (`.ok`/`.err`) records the
  variant-tag test for scalar and text payloads. Text results are also marked
  decoded.
- `dict_get_preserve_flat_nil` records `raw != 3` on the tagged word for integer
  values.
- The let-binding copy propagates the entry to the binder. Reassigning a local
  clears it (`-1`).
- `== nil` / `!= nil` against a word with a recorded bit returns that bit (or
  its negation), before any fold or word compare.
- ExistsCheck on a base that already carries a bit uses the bit and takes the
  word as the decoded payload. That removes the dict-hit double decode
  (`rt_value_as_int_wide` on an already-decoded int).

## Specs

- `test/01_unit/compiler/mir/if_val_presence_test_spec.spl` lowers in bootstrap
  mode. It has two groups:
  - Reproduction: call, annotated local, parameter.
  - Generalization: field, `elif val`, `.ok`, `[i64?]` element, `d.get`, `while val`.
  Each asserts the branch into the if-val body is `rt_is_some`, a Result-tag
  `Eq`, or a dict raw-word `Ne`. It was red 0/2 before the fix and is green 2/2 after.
- Native oracle: `test/fixtures/native_if_val_presence/main.spl`.

## Not fixed here (separate defects, still red natively after this fix)

- `[i64?]` element payload: ExistsCheck's runtime-value arm decodes the Option
  HANDLE (`decode_runtime_value(base_local)`) instead of its raw payload. The
  None row is fixed (presence now comes from `rt_is_some`); the Some payload is
  still wrong.
- `.err` text binder printed as an integer. It may be fixed by the
  decoded-text mark, but this is unverified natively.
- LLVM `row_field` `Holder(slot: opt_int(k))`: the struct ctor stores an
  `i64?` call result through `ptrtoint ptr %lN` while the call returns `i64`
  (`llc: '%l1' defined with type 'i64' but expected 'ptr'`). This is pre-existing
  on the pre-fix Stage 2. The fixture binds the field through an annotated
  local instead.
- The seed itself prints `none` for `if val x = 3` on a plain i64 and for
  `.ok` of `Ok(3)`. These are seed-divergent rows in the fixture.
