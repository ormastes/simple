# Seed interpreter: nested struct pattern inside enum payload binds all fields to 0

- **Date:** 2026-07-16
- **Component:** Rust seed interpreter (`bin/simple run`, SIMPLE_BOOTSTRAP unset) — actually the
  seed's default JIT-first execution path (HIR/MIR lowering feeding Cranelift codegen), not the
  AST tree-walking interpreter; `SIMPLE_EXECUTION_MODE=interpret` was already correct before this fix
- **Status:** fix ready, pending seed redeploy (fixed 2026-07-17)
- **Found by:** native-build correctness campaign, parity case `nested_enum_struct_match`
  in `scripts/check/check-native-seed-parity.shs`
- **Fix:** `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`,
  `build_pattern_binding_stmts`. Patch staged at
  `/tmp/claude-1000/-home-ormastes-dev-pub-simple/33c947ae-e017-48b7-b5a6-08020378379a/scratchpad/s5_seed_interp.patch`
  (worktree `/home/ormastes/dev/wt_seedfix`). **Fix verified on a freshly built seed binary;
  deployment (redeploying `bin/release/x86_64-unknown-linux-gnu/simple`) is PENDING explicit user
  approval — the deployed binary still has the bug.**

## Root cause (confirmed)

`build_pattern_binding_stmts` (shared by both statement- and expression-position match lowering)
walks each payload sub-pattern of an enum-variant arm pattern and only had a case for a payload
sub-pattern that is a plain `Identifier`/`MutIdentifier` (`case Shape.Circle(p): ...` binds `p` to
the whole payload). A *nested* struct-destructuring sub-pattern — `Point(x, y)` inside
`Shape.Circle(Point(x, y))` — parses as `Pattern::Enum { name: "_", variant: "Point", payload:
Some([Identifier("x"), Identifier("y")]) }` (the parser cannot distinguish an enum-variant pattern
from a struct pattern written with call syntax; see `parser/src/parser_patterns.rs`). This nested
pattern shape had no handling at all in the `for` loop over payload sub-patterns — it silently fell
through and emitted no binding statement. Separately, `collect_pattern_bindings` (which computes
which names to register as locals, independent of `build_pattern_binding_stmts`) *does* recurse
into this nested pattern and registers locals for `x`/`y` — so the locals existed, but were never
initialized by any `Let` statement, keeping whatever zeroed value happened to be on the stack. The
`Circle` arm was selected correctly (discriminant check passed); only the nested field extraction
was missing.

## Fix

Added the missing case to `build_pattern_binding_stmts`: when a payload sub-pattern is
`Pattern::Enum { name: "_", variant, payload: Some(patterns) }` and `variant` resolves (via the
type registry) to a genuine `HirType::Struct` (not an actual enum variant), extract the enum's
payload (`rt_enum_payload`, indexed into the wrapper array for multi-field outer variants) once,
type it as the nested struct, then bind each identifier sub-pattern positionally via `FieldAccess`
at the struct's declared field index (`Point(x, y)` binds `x` -> field 0, `y` -> field 1 in
declaration order — the parser discards field names even for the named-field spelling
`Point(x: a, y: b)`, so there is no name to look up, only position). This mirrors the existing
`class_struct_fields` heuristic already used for *top-level* arm patterns with the same
struct-vs-enum-variant parse ambiguity.

## Symptom

```spl
struct Point:
    x: i64
    y: i64

enum Shape:
    Circle(Point)
    Empty

fn main() -> i64:
    val s = Shape.Circle(Point(x: 3, y: 5))
    match s:
        case Shape.Circle(Point(x, y)): print(x * 10 + y)
        case Shape.Empty: print(99)
    return 0
```

- Seed `run`: prints `0` — the `Circle` arm IS taken (an `Empty` arm printing 99
  proves arm selection is correct), but the nested struct pattern binds
  `x = 0, y = 0`.
- Pure-Simple `native-build`: prints `35` (correct; verified with a second value
  set `Point(x: 4, y: 7)` -> `47`, so binding is real, not accidental).

## Workaround

Bind the payload whole and use field access — `case Shape.Circle(p): p.x ... p.y`
works correctly in the seed.

## Class

Same bind-zeros landmine class as the seed's `case (a, b):` tuple pattern
(parity case `tuple_pattern_match`, already NATIVE-AUTHORITATIVE).

## Harness impact

`nested_enum_struct_match` reclassified PARITY -> NATIVE-AUTHORITATIVE
(expected `35`) in `check-native-seed-parity.shs` on 2026-07-16, since the seed
oracle is provably broken here and the seed is Rust (rebuild forbidden in the
native-build campaign; fix belongs in `src/compiler_rust` interpreter pattern
binding when the seed is next rebuilt).

## Verification (2026-07-16)

Still reproduces at origin tip 8932fcb3a148: `probe12_nested_struct_pattern_a.spl` (doc's exact repro: `Shape.Circle(Point(x:3,y:5))` matched via `case Shape.Circle(Point(x, y)): print(x*10+y)`). Oracle: `bin/simple run` → `0` (should be `35`). Nested struct pattern binds `x=0, y=0` instead of real field values; matches seed landmine exactly, still OPEN.

## Verification (2026-07-17, fix)

Freshly built seed binary (worktree `/home/ormastes/dev/wt_seedfix`, not deployed) prints `35` for
the doc's exact repro, and `47` for the doc's second value set (`Point(x: 4, y: 7)`), in both the
default (JIT) execution mode and `SIMPLE_EXECUTION_MODE=interpret`. The still-deployed
`bin/simple` continues to print `0` on the same probe, confirming the probe exercises the bug and
the fix is not yet live. `nested_enum_struct_match` can be reclassified back from
NATIVE-AUTHORITATIVE to PARITY once the fixed seed is redeployed (pending explicit user approval).
