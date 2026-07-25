# Pattern-lowering gaps — characterization (read-only)

Method: `git worktree add --detach /tmp/wt_pat_probe origin/main` (54f5b35d96c).
The checked-in `bin/release/x86_64-unknown-linux-gnu/simple` seed binary in that
worktree segfaults on trivial input (stale/mismatched build vs. the working
main-repo copy, 42.4MB vs 46.2MB, `cmp` differs at byte 17); the working
main-repo seed binary (`bin/release/x86_64-unknown-linux-gnu/simple`, prints
the "bootstrap seed only" warning) was copied into the worktree purely as a
test artifact to run oracle/native — no repo source was touched. Oracle:
`env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`. Native:
`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o p.bin --clean`.
Syntax confirmed against `doc/07_guide/quick_reference/syntax_quick_reference.md`
(tuple destructure: lines 807-808, 1049) and `doc/07_guide/language/syntax.md`
(enum, line 384). Note: `syntax_quick_reference.md` lines 1396-1417 document
bare-name **enum construction** (`val kind = Panel`) as a *future* RFC feature
— that is a different construct from a bare variant used as a **match
pattern** (`case Green:`), which has no such "not yet supported" disclaimer
anywhere in the docs and works fully in the oracle interpreter (see table).

## Repro table

| # | case | oracle | native build | native run | verdict |
|---|------|--------|---------------|------------|---------|
| 1 | `val (a,b) = (1,2)` then `print(a); print(b)` | prints `1`, `2` | **fails**: `error: HIR lowering error ...: unresolved name: a` / `: unresolved name: b` | n/a (no binary) | BUG — confirmed, loud error |
| 2a | match **stmt**, unqualified, no-payload, with wildcard: `case Green: print(7)` / `case _: print(0)` | prints `7` | builds, **no diagnostic** | prints **nothing** (exit 0) | BUG — silent drop, confirmed |
| 2b | match **stmt**, qualified: `case Color.Green: print(7)` / `case _: print(0)` | prints `7` | builds clean | prints `7` | OK |
| 2c | match **expr**, unqualified: `val x = match c: case Green: 7 / case _: 0` | prints `7` | **fails loudly**: `error: HIR lowering error ...: unresolved name: Green` | n/a (no binary) | BUG — different failure mode (loud, not silent) |
| 2d | match stmt, unqualified, exhaustive, **no** wildcard (`Green`/`Red`/`Blue` all bare) | prints `7` | builds, no diagnostic | prints **nothing** (exit 0) | BUG — silent drop persists without a wildcard arm |
| 2e | match stmt, unqualified **with payload**: `case Circle(r): print(r)` / `case _: print(0)` | prints `9` | builds clean | prints `9` | OK — payload-carrying bare variant pattern already works |

Case 2e is the key differential clue: bare variant patterns *with* a payload
(`Circle(r)`) already work natively; only bare *payload-less* variant patterns
(`Green`) are broken. That asymmetry is exactly explained below.

## Gap 1 root cause — tuple destructure

`val (a, b) = (1, 2)` is **not** a distinct AST/HIR node. The parser encodes it
as an ordinary `StmtKind.Val` whose name is the literal text `"(a,b)"`:
- `src/compiler/10.frontend/core/parser_stmts.spl:1250-1291`
  (`parse_tuple_destructure_val`, comment at 1251-1253: "The evaluator detects
  the '(' prefix and destructures at runtime").

Only the **interpreter** decodes that convention:
- `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:174-175` (and
  207-208 for `var`) — `if name.starts_with("("): return
  eval_tuple_destructure(name, init_val)`
- `eval_tuple_destructure` at lines 147-164 — splits `"(a,b,c)"` on `,` and
  `env_define`s each part against the evaluated tuple's elements.

**The native HIR-lowering path never special-cases this.**
`src/compiler/20.hir/hir_lowering/statements.spl`, `lower_hir_stmt`, the
`StmtKind.Val` branch (~lines 79-101) does:
```
val v_name = ... # "(a,b)" literally
val v_symbol = self.symbols.define(v_name, SymbolKind.Variable, ...)
return HirStmt(kind: HirStmtKind.Let(v_symbol, v_hir_type, v_hir_init), ...)
```
This defines exactly **one** symbol whose name is the string `"(a,b)"`. No
symbol named `a` or `b` is ever created, so any later reference to `a`/`b`
hits "unresolved name". (The `StmtKind.Var` branch, same file, ~line 102+, has
the identical gap for `var (a,b) = ...`.) A repo-wide grep confirms no
`starts_with("(")` check exists anywhere under `src/compiler/20.hir/` or
`src/compiler/50.mir/` — the interpreter is the only lowering stage that knows
about this encoding.

### Minimal-fix sketch (statements.spl — NOT the fenced file, no lane conflict)

Both HIR node kinds needed already exist, so this needs **no new HIR
variants**, only new logic in `lower_hir_stmt`'s `Val`/`Var` branches:
- `HirStmtKind.Block(block: HirBlock)` — already in
  `src/compiler/20.hir/hir_definitions.spl:662` — lets one `Stmt` still lower
  to exactly one `HirStmt` (all 3 call sites in
  `hir_lowering/expressions.spl:797,851,862` push a single `HirStmt` per loop
  iteration and need no changes).
- `HirExprKind.TupleIndex(base: HirExpr, index: i64)` — already in
  `hir_definitions.spl` (~line 424) — for reading back element `i`.
- `HirExprKind.Var(symbol: SymbolId)` — already in `hir_definitions.spl`
  (~line 419) — to reference the temp binding.

Sketch, in `lower_hir_stmt`'s `StmtKind.Val` arm (statements.spl ~line 79),
right after `v_name` is extracted (mirror in the `Var` arm too):
```
if v_name.starts_with("("):
    val inner = v_name.slice(1, v_name.len() - 1)
    val parts = inner.split(",")
    val tmp_sym = self.symbols.define("__tuple_destructure$" + <fresh_id>,
                                       SymbolKind.Variable, nil, s.span, false, false, nil)
    var block_stmts: [HirStmt] = [
        HirStmt(kind: HirStmtKind.Let(tmp_sym, nil, v_hir_init), span: s.span)
    ]
    var pi = 0
    while pi < parts.len():
        if parts[pi] != "_":
            val part_sym = self.symbols.define(parts[pi], SymbolKind.Variable, nil, s.span, false, false, nil)
            val idx_expr = HirExpr(kind: HirExprKind.TupleIndex(
                HirExpr(kind: HirExprKind.Var(tmp_sym), type_: nil, span: s.span), pi
            ), type_: nil, span: s.span)
            block_stmts = block_stmts.push(HirStmt(kind: HirStmtKind.Let(part_sym, nil, idx_expr), span: s.span))
        pi = pi + 1
    return HirStmt(kind: HirStmtKind.Block(block: HirBlock(stmts: block_stmts, has: false, value: <unit>, span: s.span)), span: s.span)
```
Needs a fresh-name generator for the temp symbol (any existing lowering
counter/gensym helper in `HirLowering` works; if none exists, a per-lowering
`self` counter field is the smallest addition). Apply the identical change to
the `Var` branch a few lines below. No MIR-layer change should be required
since `Block`/`Let`/`TupleIndex`/`Var` are all already consumed by MIR
lowering for other constructs.

## Gap 2 root cause — unqualified variant pattern silently dropped

This is a **two-stage** bug, confirmed by reading (not editing) the fenced
`switch_operators_calls.spl` plus its caller `expr_dispatch.spl`.

### Stage A — frontend mis-classifies the bare pattern

`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`,
`convert_flat_pattern`:
- Payload-carrying bare variant (`Circle(r)`, `ptag == EXPR_CALL` with an
  `EXPR_IDENT` callee, lines 749-761) is **already special-cased**:
  ```
  # Bare variant pattern `Circle(r)` (no enum qualifier). Keep the
  # variant name and an empty enum name; MIR lowering resolves it
  # against the registered enums (never silently a Wildcard, which
  # made these arms fall through).
  return Pattern(kind: PatternKind.Enum("", bare_variant, EnumPatternPayload.Tuple(bsub)), span: pspan)
  ```
- Payload-less bare variant (`Green`, `ptag == EXPR_IDENT`, **lines 767-771**)
  has **no equivalent special case**:
  ```
  elif ptag == EXPR_IDENT:
      val nm = expr_get_str(pat_eid)
      if nm == "_":
          return Pattern(kind: PatternKind.Wildcard, span: pspan)
      return Pattern(kind: PatternKind.Binding(nm, false), span: pspan)
  ```
  `Green` unconditionally becomes `PatternKind.Binding("Green", false)` — an
  ordinary (irrefutable) binding pattern, indistinguishable from `case x:
  print(x)`. This is the same fix someone already applied for the
  payload-carrying sibling, just never mirrored to the payload-less case.

`lower_pattern` in `src/compiler/20.hir/hir_lowering/expressions.spl:697-699`
faithfully carries this through to `HirPatternKind.Binding(symbol, mutable)`.

### Stage B — MIR dispatch treats the mis-classified arm as a duplicate default and bails silently

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `lower_match_case`:
- Lines 1434-1446 decide whether to route to the enum-aware
  `lower_enum_match` (in the fenced `switch_operators_calls.spl:658`) by
  scanning for **any** arm whose `pattern.kind` is `Enum(_,_,_)`:
  ```
  var has_enum_arm = false
  ...
  case Enum(_, _, _): has_enum_arm = true
  ...
  if has_enum_arm: return self.lower_enum_match(scrutinee, arms)
  ```
  Because `Green` lowered to `Binding` (not `Enum`), `has_enum_arm` stays
  `false` for arm-lists like `[Green, _]` or `[Green, Red, Blue]`, so the
  match is routed to the **int-literal Phase-1/2a path** instead — never
  reaching `lower_enum_match`, which (at
  `switch_operators_calls.spl:718-723`) *would* have handled a stray
  `Binding` arm correctly as a plain default.
- Inside that int-literal path (lines 1469-1512), a `Binding` arm is *also*
  treated as an irrefutable default (mirrors `Wildcard`, lines 1495-1512:
  `has_default_body = true; default_body_value = arm.body`). When the arm
  scan then reaches the **next** default-like arm — the real
  `case _:` wildcard, or in the no-wildcard variant the next bare
  `Red`/`Blue` (also mis-classified `Binding`) — the duplicate-default guard
  fires (lines 1500-1508 / 1471-1479):
  ```
  if has_default_body:
      self.error("B5b: match has multiple wildcard/binding default arms", Some(arm.span))
      ... return t_dup   # empty unit temp, no int_cases dispatch emitted, no body lowered
  ```
  This **discards every arm body** (neither `Green`'s `print(7)` nor the real
  wildcard's `print(0)` is ever lowered into MIR) and returns immediately.
- Confirmed by direct evidence: re-running native-build for case 2a with full
  (unfiltered) log capture shows **no** "multiple wildcard/binding default
  arms" text anywhere in the output — `self.error(...)` records into an
  internal `MirError` list (see `module_lowering.spl:57`,
  `val empty_errors: [MirError] = []`) that is never surfaced to the
  native-build CLI output for this path. That silent diagnostic-swallowing is
  what turns a (logically) reported compiler error into the observed
  "compiles clean, runs, prints nothing" behavior — matches the "only
  rt_enum_new+ret remain" MIR characterization in the task brief.
- Case 2c (`val x = match c: case Green: 7 / case _: 0`, an
  **expression**-position match) hits a *different, earlier* failure:
  `"unresolved name: Green"` at HIR-lowering time, before MIR dispatch is
  reached at all — i.e. expression-position match lowering resolves/binds
  differently than statement-position (not traced further here; flagged as a
  second, louder symptom of the same Stage-A misclassification, worth a
  follow-up probe by the owning lane).

### Minimal-fix sketch (two independent, additive changes; neither touches the fenced file's core lowering logic beyond the `has_enum_arm` scan)

1. **Frontend** (`convert_nodes.spl`, `convert_flat_pattern`, the
   `ptag == EXPR_IDENT` branch, lines 767-771): mirror the payload-carrying
   fix. Instead of unconditionally returning `Binding(nm, false)` for a
   non-`_` identifier, return
   `Pattern(kind: PatternKind.Enum("", nm, nil), span: pspan)` and let MIR's
   existing bare-variant resolver (`switch_operators_calls.spl:695-714`,
   the "resolve the variant name against every registered enum" logic
   already written for the `Circle(r)` case) decide: if `nm` matches exactly
   one registered enum variant, treat it as `Enum`; otherwise (genuinely no
   enum declares a variant named `nm`) it must still fall back to `Binding`
   so ordinary `case x: print(x)` bindings keep working. Since
   `convert_flat_pattern` runs in the frontend (before the enum registry is
   populated), the disambiguation must happen downstream — the cleanest
   place is `switch_operators_calls.spl`'s existing variant-name-vs-registry
   scan (695-714): if `owner_count == 0` there, it should **fall back to a
   `Binding`-equivalent default arm** (what today happens for a true
   `Binding`) rather than emitting an "unknown variant" error, since a plain
   `Enum("", nm, nil)` pattern with zero matching enum owners is
   ambiguous-by-construction with "this was actually meant to be a capture
   variable". This requires `HirPatternKind.Enum` (not just `Pattern.Enum`)
   to reach that logic for payload-less arms too, i.e. `lower_pattern` in
   `expressions.spl:727-749` already handles `Enum` uniformly regardless of
   payload, so no changes needed there.
2. **MIR dispatch** (`expr_dispatch.spl`, `lower_match_case`, lines 1436-1446):
   even with fix (1) in place, a mixed arm list like `[Enum("", "Green", nil),
   Wildcard]` will correctly set `has_enum_arm = true` and route to
   `lower_enum_match`, which already handles `Wildcard`/`Binding` defaults
   correctly (lines 718-723, 807-815) — so fix (1) alone should resolve gap 2
   for the statement case. As a **defense-in-depth** measure independent of
   fix (1), the duplicate-default `self.error(...)` calls at lines
   1471-1479 and 1500-1508 should have their `MirError` list actually
   surfaced/checked by the native-build driver (or the compiler should treat
   any non-empty `MirError` list as build failure) — right now a real,
   already-authored diagnostic is silently discarded, which is what let this
   whole bug masquerade as "compiles clean, does nothing" instead of a clear
   build error. This second fix is a general error-plumbing gap, not
   specific to pattern lowering, and should probably be filed/fixed
   separately from (1).

## Cleanup

Worktree removed: `git worktree remove --force /tmp/wt_pat_probe` (only a
copied test binary and throwaway `.spl` probe files were added under it,
never committed; no source files were edited anywhere, in the worktree or in
the main repo).
