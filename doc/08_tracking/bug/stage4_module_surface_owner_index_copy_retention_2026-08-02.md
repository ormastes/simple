# Stage4 module-surface owner-index copy retention

## Status

Fixed in this change; fresh end-to-end Stage4 RSS measurement is pending the
single authorized bootstrap cycle owned by the Stage4 correctness lane.

## Measured problem

`ModuleSurfaceBuilder.resolve_export_origins` collected six declaration
categories by repeatedly assigning `declaration_names = declaration_names +
category.keys()`. In the native no-GC Stage4 process, each cumulative array is
retained after the owner index has consumed it.

A static scan of top-level declarations in the checked Stage4 source roots
(`src/compiler`, `src/lib`, and `src/app`) found 86,247 declarations across
11,279 `.spl` files. The six cumulative prefixes copy 496,684 reference slots,
5.76 slots per declaration. This is a conservative whole-root inventory, not a
claim that every file belongs to the current 1,197-file entry closure.

After the rewrite, cumulative copied reference slots are 0. The six required
`Dict.keys()` traversals remain, so this claim excludes their traversal and
key-array costs.

## Fix and preserved behavior

Visit each category key array directly in the existing order: callables,
composites, enums, traits, type aliases, constants. Keep the original owner-key
collision logic byte-for-byte in each loop. This preserves both behaviors that
could be lost by a helper or reordered merge:

- declarations sharing a name and physical source remain attributable to that
  source;
- a declaration in the last category is indexed even when the first five
  categories are empty.

Focused tests cover those exact and adjacent cases. Existing module-surface
resolution tests remain the broader semantic evidence.

## End-to-end evidence fields

Do not claim an RSS or elapsed-time improvement without recording all of:

- source revision and whether it contains this fix;
- process ID and command;
- elapsed time and phase at each sample;
- peak RSS and terminal phase/result;
- a comparable pre-fix row at the same elapsed time and phase.

The current Stage4 continuation plan is accurate in calling the earlier compact
implementation-surface optimization unmeasured; its `full-resource` wording is
procedural, not a quantitative acceptance threshold.

## Verification

- `module_surface_owner_index_spec.spl`: 2 examples, 0 failures.
- Optimizer O3: 178 generic opportunities in `module_surface.spl`; 4 generic
  opportunities in the focused spec. None is specific to this rewrite.
- `simple check src/compiler` was attempted once and was inconclusive: spawned
  workers resolve the hard-coded isolated-worktree path `bin/simple`, which is
  absent. No source diagnostic preceded that infrastructure failure.
