# HIR unit specs run longer than 300 s (hang) on the seed

- **Found:** 2026-11-06 during the W2b before/after directory runs (data plan W2b).
- **Seed:** a Rust seed built from release `4d7dda0c117`, which includes the W2a change.
- **Tree:** the unmodified base `4d7dda0c117`, so the hangs are pre-existing and do not come from W2b.
- **Specs:** each ran past 300 s with no output and was killed. Before W2a's seed rebuild, `module_surface_semantic_projection_spec` also ran past 12 min.
  - `test/01_unit/compiler/hir/module_surface_semantic_projection_spec.spl`
  - `test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl`
  - Only these two hit the 300 s reaper in that run, which covered 139 of the directory's 287 specs before it was stopped.
- **Repro:** `simple test test/01_unit/compiler/hir/module_surface_semantic_projection_spec.spl`. The `[route] mode=interpreter` line prints, then the process stays busy with no further output.
- **Expected:** a verdict, or a failing assertion, within the runner's per-file budget. A hang is a defect: it blocks every directory-lane run of `test/01_unit/compiler/hir`.
- **Next step:** run each spec with `SIMPLE_JIT_STRICT=0` and a stack sampler to find the looping pass. Whether the cause is the seed interpreter or the spec's own fixture size is not known yet.

## Re-run 2026-11-08 (Windows, `C:/dev/simple/bin/simple.exe` seed, release/1.0.0 sparse worktree)

- `field_index_erased_receiver_spec.spl`: **no longer hangs** — finishes in 10 s with
  `outcome=ERROR executed=1 failed=1`. The failure is environmental, not a loop: every
  receiver shape reports `BUILD-FAILED: absolute runtime/workspace required` (the spec
  native-builds probes and needs an absolute runtime/workspace, absent in this checkout).
- `module_surface_semantic_projection_spec.spl`: **still exceeds budget** — killed by the
  kill_monitor watchdog at 318 s (exit 143, `reason=child-died-early`), no example output.
  The spec's own docstring says it loads the full frontend in-process (`parse_and_build_module`
  + `module_surfaces_from_modules`) and to "expect a multi-minute interpreter run", so this is
  interpreter cost of the fixture, not yet proven an infinite loop.
- Still open: needs a stack sample (`SIMPLE_TIMEOUT_SECONDS=3600` run to completion, or a
  sampler) to decide between "slow but terminates" (move to a slow/perf lane, or split the
  scenarios) and a real loop in the projection. Not fixable in a lib-only lane without that data.

## 2026-11-09 note (PR #7883)
Still open. The bare-path scan hang in `module_path_naming.spl` is worked around with typed
`byte_len` bindings; root cause is `seed_untyped_byte_len_binding_raw_i64_misdecoded_2026_11_09`.
The spec file is still slow and 4 scenarios still fail, so this row is not resolved. Known twin:
`src/compiler/bootstrap_admission/stage2_module_path_naming.spl` keeps the untyped form.

## 2026-11-09 root cause + fix (hang) — fix-implemented-verification-pending
Root cause: the pure-Simple bitfield parser (`_ParserDecls/bitfield_aop_arch_decls.spl`)
did not accept the seed's bare bit-width field form `mode: 4`
(`compiler_rust/parser/src/types_def/bitfield.rs` parses an integer width). The IntLit was
never consumed, so the field loop re-reported the same parser errors forever — the
"changes for bitfield widths" scenario never returned (probe: a single
`parse_module_silent_checked("bitfield Flags(u32):\n    mode: 4\n ...")` hit the 400 s
watchdog; `mode: u4` parses in seconds). Fix: accept `name: N` as `uN`, plus a
forward-progress guard in the field loop. New `test/01_unit/compiler/parser/bitfield_bare_width_spec.spl` 4/4.
`module_surface_semantic_projection_spec` now finishes in ~72 s (was >3600 s, killed):
12 executed, 7 passed, 5 failed — sort-comparator hoist, field defaults/array-size,
export route, unresolved imports, bitfield widths/extend payload. Those are semantic-identity
assertion failures, not hangs; tracked as the remaining work on this row.

## Fix (2026-11-13) — 4 of the 5 residual semantic-identity failures

Re-run on release/1.0.0 `9777875d0d2` with the Rust seed: the hang is gone (78 s,
12 executed, 7 passed, 5 failed). Causes of the five:

1. **Sort comparator oracle stale.** `4183b795175` moved the comparator to
   `byte_len()`; the spec still grepped for `len()`. Oracle updated (same shape).
2. **Export route / resolved origin and 3. eager vs lazy imports.** The frozen
   identity digest `_module_surface_final_semantic_digest` (declaration limbs +
   import targets/lazy flag/items, export routes, friends, internal exports,
   sorted export origins) and its publish step in `module_surfaces_freeze` were
   deleted by the `4edef8fab8e` whole-tree snapshot. Restored in
   `module_surface_registry_index.spl`; sorting reuses
   `module_surface_resolution_rows_sorted_v1`.
4. **Extend payload (the bitfield half already passed).** `extend_decls.spl` resolved a bare payload
   `T` through `named_type_find`, which returns a raw named-type registry index,
   not a type tag, so `convert_flat_type` read it as a fixed tag (`text` came back
   as `bool`, as did `i64`). Now parses the full type first, like the enum variant
   loop.

After: 11/12 passed. **Still red: the array-size half of "field defaults and
array-size expressions".** The pure-Simple parser carries a fixed array size only
on the `par_fixed_array_*` side channel used by `val/var` declarations; struct
field types are bare tags, so `[i64; 2]` and `[i64; 3]` bridge to the same
`TypeKind.Array(i64, nil)`. Retaining it needs a per-field size in the flat decl
nodes and the bridge. That is a parser/AST change, left open on this row.

## Fix (2026-11-13, n2) — struct field `[T; N]` size carried to the AST

The struct-field parser (`_ParserDecls/fn_struct_decls.spl`) now resets the
`par_fixed_array_*` side channel before each field type. When the field's own
top-level type is the sized array, it records the literal N in a new per-decl pool,
`decl_field_array_sizes` (`_Ast/decl_nodes.spl`). That pool is mirrored at every
touchpoint of the `decl_field_bits` pool, and `FLAT_POOL_CODEC_VERSION` is bumped
to v16. The bridge (`module_assembly.spl` `flat_field_sized_type`) re-attaches N as
`TypeKind.Array(elem, Some(IntLit(N)))`. HIR still lowers the array as dynamic
(`types.spl` `HirTypeKind.Array(_, None)`), so the change affects only AST/surface
identity, not codegen.
`module_surface_semantic_projection_spec` passes 12/12 on the seed (about 105 s). Neighbour results:
`flat_pool_codec_roundtrip_spec` 18/18 and `bitfield_bare_width_spec` 4/4 pass.
`decl_metadata_lifetime_spec` (1 failure) and `facet_flat_decl_codec_spec`
(2 failures) fail identically with and without this change.
