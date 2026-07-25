# Match Guard Clauses on Native --entry Path — Characterization + Fix

Worktree: /tmp/wt_guards @ 35c4b52ead6, healed with ed26f0f0159 files
(lexer_struct.spl, parser.spl, mir_types.spl, mir_instructions.spl,
module_assembly.spl) per coordinator instruction. Patch:
`scratchpad/match_guards.patch` (3 files, +79/-4). NOT committed.

## Characterization (before fix)

Guards parse fine (flat AST `arm_get_guard`, HIR `has_guard`/`guard`
desugared pair all populated). The defect was downstream, and differs by
match POSITION:

1. **Statement-position guarded match** (`match n:` with `return` arms):
   reaches `lower_match_case` (50.mir/_MirLoweringExpr/expr_dispatch.spl),
   which correctly REJECTS guards via `self.error(...)` — but
   `MirLowering.errors` was NEVER READ by the native-build worker's
   `lower_to_mir` (80.driver/driver_pipeline.spl). The error was silently
   dropped, codegen proceeded on broken MIR (empty fn body), and llc crashed
   with `bitcast void %l2 to i64 / void type only allowed for function
   results` — a loud-but-cryptic backend crash far from the source. No
   binary was ever produced, so this was loud-fail with a terrible message,
   NOT silent-wrong.

2. **Value-position guarded match** (`val r = match n: ...`): never reaches
   `lower_match_case` at all. Root: value-position match desugar loses
   BINDING pattern symbols entirely (guard or not) — the guard/arm exprs
   referencing the binding hit HIR `unresolved name: x`, decay to
   `HirExprKind.Error`, and `HirLowering.errors` was ALSO silently dropped
   by the driver — llc then crashed with `use of undefined value '%l2'`.

## Root causes fixed (2 dropped-error buckets + 1 belt-and-braces)

1. **driver_pipeline.spl** (`lower_to_mir`, direct/entry-closure branch):
   promote allowlisted `MirLowering.errors` into `ctx.errors` via new
   `_mir_error_is_fatal(message)` (prefix: `"match guards (case x if cond:)
   are not supported"`). Build now fails EARLY with:
   `error: MIR lowering error: match guards (case x if cond:) are not
   supported by native codegen yet (B5b Phase 2)`.
2. **driver.spl** (`lower_and_check_impl` per-source loop): promote
   allowlisted `HirLowering.errors` via new `_hir_lowering_error_is_fatal`
   (prefix: `"unresolved name:"`). Value-position guard/binding failures now
   fail with `HIR lowering error in <module>: unresolved name: x` instead of
   an llc verifier crash.
3. **expr_dispatch.spl** (`lower_match_case` guard branch): clearer message
   + belt-and-braces `rt_panic("match guards ... not supported ...")` emitted
   in place of the arm (same proven pattern as `lower_for_iterator` #143),
   so any pipeline that still drops MirLowering.errors aborts at runtime
   with the message rather than crashing on dangling SSA.

Why allowlist, not blanket-fatal: MirLowering also records benign
diagnostics on WORKING builds (e.g. `unsupported MIR type kind:
HirTypeKind::Infer((0,0))` fires on `val x = add(3,4)` yet the binary is
correct, rc verified). Blanket-fatal would newly break those; verified
empirically.

## Battery (by construction; oracle unreliable for guards per #162)

All guarded shapes → build FAILS loudly, exit=1, NO binary, 0 llc crashes:

| shape | result |
|---|---|
| `case x if x > 5:` + `case x:` (stmt pos, n=3/n=9 program) | clear guard diag |
| literal arm guard `case 1 if n > 100:` + `case _:` | clear guard diag |
| two guarded arms + unguarded fallback | clear guard diag |
| guard w/ bound-var arithmetic `case x if x * 2 == 14:` | clear guard diag |
| inline-body stmt-pos `case x if x > 5: return 1` | clear guard diag |
| value-pos `val r = match ...` w/ guard (multi-construct w/ loop) | clear `unresolved name: x` diag |
| value-pos block-body guard | clear `unresolved name: x` diag |

Regressions (hand-computed expected rc, all pass):
- arith+fn call → rc 7 ✓; two calls into vals → rc 18 ✓ (Infer diag stays benign)
- guard-free value-pos match `case 1:`/`case _:` on matching value → rc 110 ✓ (multi-construct: match + while loop)
- trivial `print(41)` builds (runtime print-int segfault is a pre-existing
  print-ABI quirk, unrelated; rc-style programs verified instead)

## Smoke matrix

`sh scripts/check/native-smoke-matrix.shs` with fix applied (healed base):
**15/15 PASS, fail=0, xfail=0, xpass=0, codegen_fallback_hits=0, exit 0.**
Exceeds the >=14/15 gate; even the allowed-fail option_nil_check passes.
(Baseline on the un-healed 35c4b52ead6 base: ALL 15 build-failed — broken
base, not this change; coordinator confirmed and supplied the heal set.)

## NEW BUG DISCOVERED (separate item, silent-wrong, needs own lane)

**Value-position match ALWAYS takes the first arm** (guard-free!):
```simple
fn classify(n: i64) -> i64:
    val result = match n:
        case 1: 10
        case _: 20
    return result
fn main() -> i64: return classify(9)   # returns 10, must be 20
```
Builds clean, runs, returns the FIRST arm's value for any scrutinee.
Same family as the binding-symbol loss: the value-position match desugar
(parser/bridge — bridge only handles STMT_MATCH; no EXPR_MATCH conversion
exists in _FlatAstBridge/convert_nodes.spl) is broken. The interpreter side
is #162-adjacent. This is SILENT-WRONG on guard-free code and should be
prioritized. Not fixed here (out of ONE-ITEM scope: guards).

## Conflict flags

- **NO edits to switch_operators_calls.spl** (owned by operator-overloading
  lane) — NOT conflict-flagged.
- Edited: expr_dispatch.spl (allowed per brief), driver.spl,
  driver_pipeline.spl.
- Note: driver_pipeline.spl / driver.spl are broadly-shared driver files;
  edits are additive (new fns + two promotion loops), low conflict risk.
