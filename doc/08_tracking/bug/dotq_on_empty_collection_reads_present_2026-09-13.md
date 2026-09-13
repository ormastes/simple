# BUG: `.?` on an empty collection reads as PRESENT, so `while coll.?:` never terminates

- **Filed:** 2026-09-13
- **Status:** OPEN (2026-09-13)
- **Lane:** BOOT-9 (bootstrap site 9)
- **Severity:** High — a `while <collection>.?:` drain loop diverges, allocating
  without bound. It is not a wrong ANSWER, it is a program that never returns.
- **Supersedes/reopens:** `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27.md`
  (CLOSED-STALE, "reopen with a fresh repro against the current seed"). This is
  that fresh repro, narrowed to the empty-collection row.

## Specification (not in dispute)

`doc/07_guide/quick_reference/syntax_quick_reference.md:537-549`:

```
list.?    # [T]?: Some(list) if non-empty, nil if []
dict.?    # {K:V}?: Some(dict) if non-empty, nil if {}
str.?     # text?: Some(str) if non-empty, nil if ""
```

and `:648` — `list.is_empty()` is spelled `not list.?`.

## Measured — seed `simple run` lane, binary sha256 `3d120a6f9ab5704b...`

Probe `scratchpad/boot9/probe/basic2.spl`, one variable per row:

| form | receiver | measured | spec |
|---|---|---|---|
| `if e.?:` | `var e: [i64] = []` | **true** | false |
| `if not e.?:` | same | **false** | true |
| `while w.?:` (break at 5) | `var w: [i64] = []` | **6 iterations — never exits** | 0 iterations |
| `while s.len() > 0:` + `s.pop().unwrap()` | `[(i64, bool)]`, 2 items | 2 iterations, drains, terminates | same |

## Measured — native codegen, Stage-2 candidate sha256 `95763bffee64a74e...` (152199352 B)

`BuildGraph.topological_order` (`0x381b228`), loop head `0x381b350`:

```
381b350: mov  x0, x23            ; x23 = the stack ARRAY
381b354: bl   3f10cbc <rt_is_some>
...
381b36c: b.ne 381b2a8            ; the ONLY exit from the while loop
```

`rt_is_some` is `!rt_is_none` (`src/compiler_rust/runtime/src/value/objects.rs:546-560`)
and `rt_is_none` answers true only for nil or an Option enum with the None
discriminant — never for an array, empty or not. So the exit branch is dead
code and the loop is unbounded.

## Why both lanes emit it

Both lowerings drop the emptiness half of `.?` and call `rt_is_some` on the
RECEIVER:

- pure-Simple MIR: `src/compiler/50.mir/mir_lowering_stmts.spl:2634-2645`
  (`lower_cond_operand`, `case HirExprKind.ExistsCheck`) and
  `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4135-4212`
  (value position).
- Rust seed HIR: `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2080-2088`
  (`lower_condition`) and `:2344-2405` (`lower_exists_check`).

The seed's TREE-WALK interpreter is the one implementation that is correct
(`src/compiler_rust/compiler/src/interpreter/expr.rs:533-568` explicitly
returns `Value::Nil` for an empty Array/Dict/Str), which is why the 2026-07-27
record said "the interpreter is correct" — but the default `simple run` lane
does not use it for this code, and the table above is what that lane does.

## Blast radius — census of collection-receiver `while X.?:` in `src/` (2026-09-13)

| site | receiver | disposition |
|---|---|---|
| `src/compiler/80.driver/driver_build/parallel.spl:285` | `[(i64, bool)]` | **FIXED** by this lane (`while stack.len() > 0:`) — it was the Stage-2 admission blocker |
| `src/compiler/90.tools/context_pack.spl:58` | `[text]` | untouched: the path is FENCED for this lane (`scratchpad/egl_offlimits_v2.txt`) |
| `src/compiler/10.frontend/parser/test_analyzer.spl:233` | `[TestGroup]` | untouched: outside the admission path. Open question, recorded not asserted — this flush loop should diverge by the same reading, yet test runs do not hang, so the function is probably demoted to the tree-walk lane (`compilability.rs:683` says ExistsCheck "requires runtime type inspection"). Someone should measure it. |

The optional-receiver sites (`gc.spl` `while current.?:`, `persistent_symbol_table.spl`
`while scope_id.?:`) are correct uses and are NOT affected.

## Not fixed here, deliberately

Changing `.?`'s lowering means changing a language operator on two engines at
once; `test/01_unit/language/nil_presence_idioms_spec.spl` already refuses to
assert this row so as not to freeze the bug. The bootstrap blocker was fixed at
its one call site instead. A real fix needs a presence predicate that decodes
collection emptiness (the tree-walk implementation is the reference) wired into
both `lower_condition` paths, plus the value-position arms.
