# Compiler Context Registry Memory Audit

## Finding

`compiler_sffi.spl` stored every live compiler-context handle twice: once as the
key of `CONTEXT_REGISTRY` and again in `CONTEXT_HANDLES`. Destroying one context
rebuilt and copied the complete registry and handle array, producing O(n) work
and O(n) transient storage per close.

## Fix

Use the dictionary's existing O(1)-class `remove` operation and delete the
shadow handle array. Handle values, context layout, public ABI, ownership, and
alignment are unchanged.

## Measurement

For 1,024 simultaneously live contexts, registry index storage falls from at
least 2,048 index words to 1,024 index words: a 50% reduction in explicit
registry-index storage. Destroy processing falls from 524,800 inspected handle
entries to 1,024 keyed removals. The stress specification creates and destroys
1,024 real contexts and checks the retained index count returns to zero.

## Lint assessment

No lint was added. A dictionary plus a parallel array can intentionally preserve
ordering or provide a dense traversal index, so syntax alone cannot identify
this pattern without false positives. A future ownership/index-effect analysis
could flag a shadow collection only when all writes and reads prove redundant.
