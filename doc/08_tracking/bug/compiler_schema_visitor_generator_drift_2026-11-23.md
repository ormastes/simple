# compiler_schema visitor/fold generator disagrees with checked-in generated files

- id: compiler_schema_visitor_generator_drift_2026-11-23
- status: open
- severity: P2
- found: 2026-11-23 on release/1.0.0 (84ea108c7c9), while fixing hir_codec_integer_three_spec

## Repro

```
bin/simple run src/app/compiler_schema/main.spl visitors <tmp>/v <tmp>/f
diff <tmp>/v/hir_visit.spl src/compiler/20.hir/generated/hir_visit.spl
```

## Drift (generated vs checked in)

| file | differing lines |
|---|---|
| 20.hir/generated/hir_children.spl | 72 |
| 20.hir/generated/hir_hash.spl | 56 |
| 20.hir/generated/hir_visit.spl | 36 |
| 20.hir/generated/hir_visitor.spl | 70 |
| 10.frontend/generated/ast_visitor.spl | 81 |

Classes:
1. The generator emits `case nil:` and `if node == nil` outside unsafe
   (`visitor_gen.spl:494,496,534`, `fold_gen.spl:515`). The checked-in files were
   hand-edited to `case None:`, so regenerating would fail the nil-outside-unsafe gate.
2. The generator emits `TargetLater(_, _)` in `ast_visitor.spl` and new walk
   functions such as `walk_hir_attr_access_kind_v1`. The checked-in files were never
   regenerated after those schema additions.
3. The `registry-hash` headers differ as a consequence.

## Fix

Make the generators emit `None` instead of `nil`, without a nil compare outside
unsafe. Then regenerate all five files in one change and check that the visitor
specs pass.
