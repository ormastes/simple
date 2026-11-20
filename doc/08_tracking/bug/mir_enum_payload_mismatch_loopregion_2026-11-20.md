# MIR enum payload mismatch at `PerfBodyNodeV1.LoopRegion` (`[T].pop()` is `T?`)

- **Date:** 2026-11-20
- **Status:** source workaround landed in `src/compiler/35.semantics/perf/cost_summary_v1.spl`; underlying compiler gap OPEN (see "Compiler gap")
- **Found by:** Phase 4 (integ22 Stage 2 compiler native-building the full CLI)
- **Fixture (green shape):** `test/fixtures/native_recursive_enum_payload_from_pop/main.spl`

## Symptom

```
[ERROR] [mir-module-failure] module=compiler.semantics.perf.cost_summary_v1 ... fatal_count=2
first=enum construction 'compiler.semantics.perf.cost_summary_v1.PerfBodyNodeV1.LoopRegion':
payload type mismatch at 1; function=summarize_hir_function_v1 ... cost_summary_v1.spl:653:70
```

The failing site is line 653 `built.push(PerfBodyNodeV1.LoopRegion(shape, built.pop(), span))`
(payload index 1 = `body`). The second fatal is the sibling `BuildBranch` arm
(`val else_node = built.pop()` / `val then_node = built.pop()` into `PerfBodyNodeV1.Branch`).
The nested-constructor site at ~618 (`LoopRegion(..., PerfBodyNodeV1.StepWork(...), ...)`) is
NOT a failure: it builds and the recursive-enum payload is typed correctly.

## Root cause

`[T].pop()` is `T?` in pure-Simple MIR: `method_calls_literals.spl` (`method == "pop"`) builds a
typed Option (via the `last()` decoder) before calling `rt_array_pop`. The source relied on the
seed interpreter, which returns the raw element. The enum-payload check is **correct** to refuse a
`T?` in a non-optional `T` slot (never widen nil).

Binding first does NOT help: `val body_node: NodeX = built.pop()` fails with the explicit
`optional 'NodeX?' value into non-optional payload slot (declared 'NodeX'); unwrap it first`.
The type-correct form is `built.pop().unwrap()` (checked unwrap, traps on empty).

## Evidence (integ22 Stage 2, `--backend=cranelift`, `SIMPLE_BOOTSTRAP=1`, MemoryMax=8G)

Stage 2: `simple-integ5-20261116/build/bootstrap/pinned-src/pinned-e1b8cc353599/build/bootstrap-s2probe-integ22/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`

| shape | result |
|---|---|
| `built.push(NodeX.Loop(shape, built.pop(), span))` | RED: `payload type mismatch at 1` (build rc=1) |
| `val body_node: NodeX = built.pop()` then construct | RED: `optional 'NodeX?' value into non-optional payload slot` |
| `NodeX.Loop(ShapeX.Linear(4), NodeX.Step(1, span), span)` then `depth(built.pop())` | builds rc=0, **runtime PANIC**: `total enum match fell through on 'NodeX'` |
| `.pop().unwrap()` at every site (committed fixture) | GREEN: builds, output `a=204 b=105` / `root=204`, identical to seed interpreter |

The committed fixture also builds and runs green on `--backend=llvm` with the same output as the
seed (`check_fx.sh`: cranelift SAME, llvm SAME).

Module-level: native-building the patched `cost_summary_v1.spl` itself as the entry module with the
same Stage 2 (cranelift) reports `phase=mir ... succeeded=158 failed=0` and zero
`mir-module-failure` lines. The build stops only at link, with `undefined symbol: __simple_main`,
which is expected because the module has no `main`. The unpatched file fails in Phase 4 with
`fatal_count=2` (above).

Red snippet (kept here, not as a fixture, so fixture-building lanes stay green):

```simple
var built: [NodeX] = []
built.push(NodeX.Step(1, span))
built.push(NodeX.Loop(shape, built.pop(), span))   # payload type mismatch at 1
```

## Workaround

Every `.pop()` in `cost_summary_v1.spl` (12 sites, two stack machines) now reads `.pop().unwrap()`.
All are guarded by a `len() > 0` loop/branch or by stack balance, so the only behavioural change is
that an impossible empty pop traps instead of yielding nil.

## Compiler gap (open)

`T?` into a non-optional `T` is rejected only for **enum payloads**. Verified silently accepted:

- function call arguments (`depth(built.pop())` above — compiles, panics at runtime on the
  Option wrapper).

Not rejected at MIR time in `cost_summary_v1.spl` (only the 2 enum-payload sites were fatal), runtime
behaviour unverified:

- `[T].push(x)` with `x: T?` (`children.push(built.pop())`),
- `match` scrutinees (`val task = tasks.pop()` then `match task:` with `T` arms),
- field access on a `T?` local (`val right_v = values.pop()` then `right_v.work`).

Those sites should get the same fail-closed MIR/HIR check (or the HIR type checker should reject
`T?` where `T` is required) so this class is caught at compile time instead of corrupting values.
