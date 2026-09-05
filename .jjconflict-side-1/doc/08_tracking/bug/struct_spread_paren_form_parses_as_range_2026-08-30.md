# Paren-form struct spread `T(..base, f: v)` parses as a RANGE, and hangs the compiler (2026-08-30)

**Status:** OPEN (feature unimplemented). Two mitigations landed; the language
feature itself is deliberately NOT attempted here.
**Area:** parser / HIR lowering / C runtime
**Severity:** blocker — hung Stage 2 on macOS on a three-line hello world

## 1. Symptom

Stage 2 compiled cleanly (`[bootstrap-error-count] 0` at parse, hir,
monomorphize, mir, aop_weave) and then HUNG — no error, no progress. macOS
`sample`, 2161 samples, all on the main thread:

```
..._storage_projection_lowering__lower_mir_storage_project_fields_v1 (+288)
  2001  rt_range (+80)
    83  rt_range (+76)
    61  rt_array_push_grow (+8)
```

## 2. Mechanism

`src/compiler/60.mir_opt/mir_opt/storage_projection_lowering.spl:247` read:

```
rewritten_functions[symbol] = MirFunction(..function, blocks: blocks)
```

That is **paren-form** struct spread. The parser accepts `..base` **only in
BRACE form** — both spread sites sit after consuming `{` and loop to `}`:

- `src/compiler_rust/parser/src/expressions/postfix.rs:472`
- `src/compiler_rust/parser/src/expressions/primary/identifiers.rs:268`

In paren form the `..` instead falls into `parse_range`
(`parser/src/expressions/binary.rs:349`), which builds a PREFIX range:

```rust
if self.check(&TokenKind::DoubleDot) { self.advance();
    ... return Ok(Expr::Range { start: None, end, bound: RangeBound::Exclusive }); }
```

So `..function` becomes `Range{start: None, end: function}` and lowers to
`rt_range(0, <MirFunction object value>)`.

**Amplifier:** `rt_range` MATERIALISES its range (`src/runtime/runtime_native.c`),
pushing one element at a time. An object value is a large positive integer well
under `INT64_MAX`, so the only existing guard did not fire and the runtime spun
for hours allocating. The defect therefore presented as a HANG WITH NO
DIAGNOSTIC rather than an error — which is what made it expensive to localise.

## 3. The feature is unimplemented end to end

Even the BRACE form does not work — the parsed `spread` is DISCARDED at lowering:

- `compiler/src/hir/lower/expr/mod.rs:176`
  `Expr::StructInit { name, fields, .. } => self.lower_struct_init(name, fields, ctx)`
  — note the `..`; `spread` is dropped, so base fields are never copied.
- `compiler/src/hir/lower/module_lowering/module_pass.rs:363`
  `if spread.is_some() { return; }`

So brace form silently produces a struct with unlisted fields unset; paren form
hangs. There is no working spelling of struct spread today.

## 4. Census (measured 2026-08-30)

| form | count in `src/**/*.spl` |
|---|---|
| paren `T(..base, ...)` | **110** |
| brace `T{ ..base, ... }` | **0** |

The tree uses **exclusively** the form that does not work. The remaining 109
sites (after the fix below) are latent hangs — including `src/lib` builders such
as `PerfConfig` (`gc_async_mut/perf.spl:76,80,84,87,90` and the `nogc_sync_mut`
twins) and `Diagnostic` (`lsp/protocol.spl:85`). Each hangs the moment it is
reached natively.

## 5. What landed (mitigations, not the fix)

1. **`storage_projection_lowering.spl:247`** now calls the purpose-built helper
   `MirFunction.with_blocks(function, blocks)`
   (`src/compiler/50.mir/mir_instruction_graph.spl:261`), which enumerates all
   **30** `MirFunction` fields explicitly. That helper already carried the
   comment *"update field list when MirFunction gains fields — spread operator
   fails cross-module"*, i.e. someone had hit this before and worked around it
   locally without filing the general defect.
2. **`rt_range` fails fast** instead of hanging: `RT_RANGE_MAX_LEN = 1<<28`
   (268,435,456). Over the cap it prints the operands, the computed length, the
   likely cause and this doc, then aborts. Deliberately an ABORT, never a clamp —
   a clamp turns a hang into a silently wrong answer. Threshold rationale:
   materialising 2.68e8 elements already costs >2 GB, so no legitimate range
   reaches it, while any heap object value (the real failure mode) is
   >= 0x100000000 = 4,294,967,296 — a 16x margin.

## 6. Real fix (NOT attempted here — deliberate)

Implement struct spread properly, as its own change:
- parser: accept `..base` in paren-form constructor argument lists;
- HIR: stop discarding `spread` at `expr/mod.rs:176` and fill every field not
  explicitly listed from the base expression.

110 call sites depend on it, so it needs its own review and test pass rather
than being done mid-bootstrap-lane.

## 7. Notes

- The Rust runtime sibling `rt_range`
  (`src/compiler_rust/runtime/src/value/collections.rs:4828`) was left unchanged;
  it has the same materialising shape and should get the same guard.
- Secondary, unrelated to the hang but real: the same function iterates
  `for symbol in module.functions.keys()` while writing `rewritten_functions[symbol]`
  inside the loop — the O(n^2) copy-on-write pattern called out in
  `.claude/rules/code-style.md`. Worth its own pass.
