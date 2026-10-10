# Method-call arguments are not coerced to Option handles for `T?` scalar parameters

**Status:** open. Found in review of the rebased nil/optional series
(`work/rel-native-nil-compare-rebased-20261010`, resolution `933101bb85e`).
**Engines:** staged-native (any compiler built by the pure-Simple MIR
lowering), both backends. The interpreter is unaffected (dynamic values).
**Parent:** `native_scalar_nil_compare_payload_bits_2026-10-10.md`, fix 5.

## Defect

The representation rule of the parent record says an Optional value is ALWAYS
the enum-id-1 handle or the bare nil sentinel, never a raw payload word. The
coercion that enforces it at a call (`ensure_option_handle` on each argument
whose parameter is declared `T?`) runs on the free-function call path only
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, the
param-directed boxing block). The method-call paths pass their arguments raw:

- `lower_receiver_and_args` (`src/compiler/50.mir/mir_lowering_stmts.spl`),
- `build_args_from_receiver`
  (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`),
- the `Unresolved` method arm in the same file.

So for `me put(v: i64?)`, `w.put(3)` hands the callee the raw word 3. Inside
the callee `v == nil` lowers to `rt_is_none(v)`, and `rt_is_none(3)` is true:
the integer 3 reads as nil. A `bool?` parameter receives raw `true`/`false`,
an `f64?` raw float bits. `v ?? d` and `if val x = v` go through the same
handle predicates and are wrong the same way.

## Evidence (lowering probe, interpreted pure-Simple lowering of this tree)

`rt_enum_new` / `rt_enum_id` / `rt_is_none` occurrences in the lowered MIR:

| function | source | enum_new | enum_id | is_none |
|---|---|---|---|---|
| `free_lit` | `take(3)` with `fn take(o: i64?)` | 1 | 1 | 0 |
| `m_lit` | `w.put(3)` with `me put(v: i64?)` | 0 | 0 | 0 |
| `m_var` | `w.put(x)`, `x: i64` | 0 | 0 | 0 |
| `m_bool` | `w.putb(x)`, `x: bool`, `me putb(v: bool?)` | 0 | 0 | 0 |
| `m_nil` | `w.put(nil)` | 0 | 0 | 0 |
| `put` (callee) | `if v == nil:` | 0 | 0 | 1 |

(Reviewer probe: `C:/dev/simple-bootstrap-storage/intensive-tests/
review_nil_rebased/method_arg_box_probe_spec.spl`, `probe.log`.)

## Why it matters

It is what made the typed HIR codec writers (`put_i64(v: i64?)`) wrong: every
one of the 1,301 `w.put_i64(...)` and 121 `w.put_bool(...)` sites in
`src/compiler/20.hir/generated/hir_codec.spl` is a method call, so
`w.put_i64(3)` would have written `N` and the HIR cache would never hit --
the bug PR #2882 fixed. The codec was therefore put back on the rendered-text
form and does not depend on this defect.

## Fix direction

Apply the same parameter-directed `ensure_option_handle` coercion the
free-function path uses at the three method-call sites, for every dispatch
kind (instance, static, trait, extension, and the `Unresolved` arm), with one
must-fail-before spec per dispatch kind.
