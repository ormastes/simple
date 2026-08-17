# Native `Option<bool>` equality against a raw bool literal returns wrong answer

Status: open
Severity: P1 native semantic parity (silent wrong output, no spec can see it)
Family: same underlying defect class as
`doc/08_tracking/bug/native_inlined_option_return_representation_mismatch_2026-08-02.md`
("row.get(...) == Some(run_id)" -- Fix owner:
`/root/native-option-return-representation`, TRACKED, NOT PARALLEL-CLAIMABLE) --
this doc is a NEW instance of that family (Option<bool> vs a raw bool literal,
not Option vs Option), found incidentally by another lane and not previously
chased. This doc does not claim ownership of the general fix; it documents,
fences, and hands the exact code location to the owning effort.

## Finding

Under `native-build`, comparing a `bool?` (`Option<bool>`) value against a raw
`true`/`false` literal (`a == true`) silently returns the WRONG answer for
every case where the correct answer is "match" -- while the interpreter and
(mostly) the JIT get it right. This is a real, silent output divergence in
compiled binaries; `bin/simple test` cannot see it (hard-defaults to the
tree-walk interpreter; no AOT `TestExecutionMode`).

Comparing `Option<bool> == Option<bool>` (`Some(true) == Some(true)`) already
works correctly on all three engines (verified via the pre-existing fixture
`test/fixtures/native_option_eq_representation` and this doc's own `p13`
probe) -- the defect is specific to Option-vs-raw-scalar comparison, not
Option-vs-Option.

## Three-engine truth table

Probes built fresh in isolation (each its own directory/module, so an
unsupported construct in one probe cannot silently demote a different probe
to the interpreter). `interp` = `SIMPLE_EXECUTION_MODE=interpret bin/simple
run`; `jit` = bare `bin/simple run`; `native` = `native-build` + run the
produced binary. `make(flag)` returns `bool?` via implicit true/false
coercion (`return true` / `return false`) unless noted "explicit Option"
(`return Some(true)` / `return Some(false)`).

| # | Expression | interp | jit | native | correct | native OK? |
|---|---|---|---|---|---|---|
| p1 | `Some(true) == true` | match | match | **no-match** | match | **WRONG** |
| p2 | `Some(false) == false` | match | match | **no-match** | match | **WRONG** |
| p3 | `nil == nil` (both `bool?`) | match | match | **no-match** | match | **WRONG** |
| p4 | `nil == true` | no-match | no-match | no-match | no-match | OK |
| p5 | `nil == false` | no-match | no-match | no-match | no-match | OK |
| p9 | `Some(true) == false` | no-match | no-match | no-match | no-match | OK |
| p10 | `Some(false) == true` | no-match | no-match | no-match | no-match | OK |
| p11 | `Some(true) == nil` | no-match | no-match | no-match | no-match | OK |
| p12 | `Some(false) == nil` | no-match | no-match | no-match | no-match | OK |
| p13 | explicit `Some(true)==Some(true)` & `Some(false)==Some(false)` | match/match | match/match | match/match | match/match | OK |
| p14 | explicit `Option<bool>` (`return Some(true)`) `== true` | match | **no-match** | **no-match** | match | **WRONG (jit too)** |

Additional divergence found while filling the required `?? default` leg of
the matrix (same `bool?` shape, different operator -- **not** `rt_native_eq`,
a separate lowering path, documented here because it was found in the same
sweep and is otherwise unfenced):

| # | Expression | interp | jit | native | correct |
|---|---|---|---|---|---|
| p6 | `Some(true) ?? false` | `true` | **`nil`** | **`1`** | `true` |
| p7 | `Some(false) ?? true` | `false` | **`0`** | **`0`** (right value, wrong repr: raw int not "false") | `false` |
| p8 | `nil ?? true` | `true` | **`nil`** | **`1`** | `true` |

The pattern: whenever the correct answer is "the boxed `Some(x)` unwraps to
`true`", native (and often JIT) prints/compares the RAW unboxed i64/i1
bit-pattern representation instead of decoding through the Option box. Rows
where the correct answer is already "no-match"/false happen to come out
right by coincidence (a raw pointer/box can never equal a small int, so a
"not equal" verdict is always reached whether or not the compiler unboxed
correctly) -- this is why p4/p5/p9-p12 look "fine" while p1/p2/p3 expose the
bug. This is exactly the trap the task brief warned about: sampling only the
"already correct" rows would have missed the defect entirely.

## Root cause (established at file:line, `.spl`-owned code)

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `lower_expr`'s
`Binary` arm, `case _:` fallthrough (line ~2559 onward):

```
var bin_is_enum_eq = false
match op:
    case Eq | NotEq:
        val left_enum_type = self.local_enum_type_id(left_local)
        val right_enum_type = self.local_enum_type_id(right_local)
        bin_is_enum_eq = left_enum_type >= 0 and left_enum_type == right_enum_type
    case _:
        ()
if bin_is_enum_eq:
    # ... routes through rt_native_eq (the boxed-aware comparator) ...
```//actual lines 2567-2594

`local_enum_type_id` (same file, lines 491-502) DOES recognize `Option` as a
registered enum (`enum_variant_index["Option"] = ["Some", "None"]`, set in
`_MirLowering/module_lowering.spl:921-922` and
`_MirLowering/bootstrap_globals.spl:544-545,655-656`), so an
`Option`-typed local correctly resolves to a non-negative enum id. The bug is
the **symmetry requirement**: `bin_is_enum_eq` only fires when BOTH operands
resolve to the SAME enum id. A raw bool literal (`true`/`false`, HIR type
`Bool`, not `Named(Option, ...)`) makes `local_enum_type_id(right_local)`
return `-1`, so `left_enum_type == right_enum_type` is false even though
`left_enum_type >= 0`. The comparison therefore falls all the way through
(past the string-eq special case at line ~2893-2937, which also does not
apply -- neither operand is str-typed) to the **generic** `emit_binop`
fallback at line ~2960, which performs a raw representation-blind compare:
the boxed `Some(true)` (an `rt_enum_new`-produced tagged pointer/handle) is
compared bit-for-bit against a raw `i1`/`i64` `true`, which can never match a
pointer representation -- hence the observed "always no-match" for every case
where the two sides are physically Option-boxed vs. raw-scalar, regardless of
logical equality.

This confirms the task's working hypothesis ("likely in the row-2 family
(`rt_native_eq` representation mismatch) with a bool payload") -- it IS that
family, but the trigger is the asymmetric-typing gate on `bin_is_enum_eq`,
not `rt_native_eq` itself (which is never reached for this shape at all).

Ownership: this code (`expr_dispatch.spl`) is `.spl`, in-lane for the pure-
Simple compiler, and IS reachable from `native-build` (MIR lowering runs for
both JIT and AOT). However the general Option representation-parity fix is
explicitly TRACKED and marked NOT PARALLEL-CLAIMABLE by
`/root/native-option-return-representation` (see the referenced 2026-08-02
doc), and that doc records a bounded/narrow mitigation attempt as ALREADY
TRIED AND REJECTED ("still returned false... removed rather than committing
an ineffective divergence"). Per that precedent and the ownership marker, no
narrow patch to `bin_is_enum_eq`/`local_enum_type_id` was attempted here --
doing so risks colliding with the owning lane's in-flight representation
work. This doc hands the exact trigger condition (asymmetric enum-id
comparison, line ~2572) to that effort instead.

The `??`-operator divergence (p6-p8) is a separate lowering path (not
`rt_native_eq`/`bin_is_enum_eq`) and was not root-caused further within this
task's scope; it is recorded here as a sibling finding for whoever picks up
the family next.

## Fence

`scripts/check/check-native-option-bool-eq-vs-literal.shs` +
`test/fixtures/native_option_bool_eq_vs_literal/main.spl`, modelled on
`scripts/check/check-native-tuple-to-text.shs`. Hard-asserts the rows that
already agree across all three engines (p4/p5/p9-p12-equivalent shapes) and
reports the p1/p2/p3-equivalent rows as `KNOWN-OPEN` with the expected-
correct value stated, so a future fix announces itself instead of needing to
be rediscovered. Sabotage-verified: mutating a hard-assert fixture line flips
the script to FAIL (exit 1); restoring returns it to PASS (exit 0).

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

UNPROVEN by this lane (native-only). The hosted half of the matrix re-checks clean on the deployed seed: `make(true) == true` where `make` returns `bool?` by implicit coercion prints `p1=true` under BOTH jit and SIMPLE_EXECUTION_MODE=interpreter, matching rows p1's interp/jit columns. The wrong-answer columns are native-build only, and native-build/`pipeline/native_project/**` is claimed by another lane, so the native leg was not re-run here. Ownership stays with the native-option-return-representation effort as the doc states.
