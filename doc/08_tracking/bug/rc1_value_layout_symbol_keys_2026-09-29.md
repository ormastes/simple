# RC1 value-layout key mismatch and remaining native diagnostics

## Concrete source defect

`HirModule.structs` is `Dict<SymbolId, HirStruct>` (`hir_types.spl`).
`value_struct_layout.spl` incorrectly declared its keys as `[text]` and fetched
struct values with a `text` key. Correcting that annotation to `[SymbolId]` was
insufficient: native dictionary lookup uses pointer identity for these erased
aggregate keys, while extracting a typed `SymbolId` copies its one-field value.
The current repair iterates `module.structs.values()` in dictionary insertion
order and explicitly types the canonical text key. It avoids reconstructing a
key to fetch a value already available directly. Traversal order, cycle
diagnostics, and the owner-index bounds guard remain.

## Native diagnostic evidence before repair

Producer: admitted cycle-3 Stage 2, `build/bootstrap/stage2/aarch64-apple-darwin/simple`.
Input: `test/fixtures/compiler/rc1_hir_block_tail.spl`, isolated diagnostic caches.

- `build/native_probe/config-layout/layout-owner-debug-symbol.log`: at validator
  offset 2884, the owner index was 3 while module-values length was 1.
  The pending walk's node key was already NIL (raw 3).
- `layout-root-isolated-debug.log` and `layout-root-raw-debug.log`: root array
  length was 1 but its backing element was NIL. Both generic `rt_index_get`
  and direct `rt_array_get` returned NIL. This disproves an initial suspicion
  that generic root iteration alone caused the failure. No root-loop workaround
  was applied.
- `layout-root-debug.log` and `layout-canonical-debug.log`: some diagnostic
  launches instead hit `EXC_BAD_ACCESS` at
  `flat_ast_to_module + 8772`, before HIR/layout validation. This remains an
  independent memory/lifetime risk; the layout key repair does not claim to
  resolve it.

## Renewed cycle 1: root cause proven

The admitted producer `build/phase_snapshots/phase1_1790649469_phase2_1790650801/simple`
still failed the block-tail fixture after the key-annotation correction.
Two bounded LLDB diagnostics captured the full causal chain:

- `layout-cycle1-canonical-debug.log`: projected `struct_.name` was raw zero;
  the module key was valid text.
- `layout-cycle1-key-debug.log`: original key pointer `0xba93074c1` and copied
  typed key `0xba9305b61` both contained `SymbolId.id = 0`. A diagnostic call
  `rt_index_get(dict, original_key)` returned the valid struct `0xba922b341`.
  The emitted lookup with the copied key returned NIL (3).
- The missing aggregate lookup was zero-filled by native aggregate extraction.
  Concatenating its zero name produced NIL; the canonical result and the actual
  `roots.push` argument were both 3. The later owner-index diagnostic was thus
  a downstream symptom of failed aggregate-key lookup.

Direct value iteration removes the unnecessary identity-sensitive lookup in
this validator. General native `Dict<SymbolId, T>` value-key equality remains
an open compiler/runtime representation bug; this local repair does not claim
to fix dictionary equality everywhere. Rebuilt execution is still required.

## Acceptance pending on rebuilt producer

- Existing `rc1_hir_block_tail.spl` must compile and execute successfully.
- `rc1_value_layout_symbol_keys.spl` must compile and execute with its PASS line
  and exit 0, proving two nested struct values retain their fields.
- `rc1_value_layout_symbol_cycle.spl` must fail compilation with
  `recursive by-value struct layout`, preserving rejection of actual cycles.
- Existing `value_struct_layout_spec.spl` covers self/mutual cycles, insertion
  order, optional/array indirection and non-cyclic shared fields.

**STATUS: WARN — source defect repaired; rebuilt native verification pending.**
