# Fresh parse and front-end cache hit lower to different HIR (span offsets) (2026-11-13)

**Binary:** `/home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple` (Rust seed,
119570696 bytes, 2026-11-05 18:12), worktree `simple-nodestore-20261113` on
`work/node-storage-phase-c-20261113` (base `bd42e7997a4`), `simple test` lane.

**Symptom.** For one parse of `src/compiler/20.hir/hir_lowering/attr_access_sites.spl`, the
boxed `ParserModule` returned by `parse_and_build_module_scoped` and the one rebuilt from the
captured pool blob of the SAME parse (`build_module_from_flat_pool_blob`, the `.fpc` line
cache hit) lower to HIR codec blobs (`hir_module_encode`) of equal length (25,718 lines) that
differ in **2,706 lines**. The packed `.spab` restore (`build_module_from_packed_view_v1`) is
byte-identical to the line-cache restore (0 differing lines), so both production cache-hit
formats agree with each other and disagree with the fresh parse. `src/lib/common/text_bytes.spl`
shows no difference.

**Shape.** The differing scalars are span fields. First difference (codec line 6347): the
empty dict literal `{}` at line 152 col 43 (`var tree_of_class: Dict<text, text> = {}`) has
`start=11 end=11 ... len=0` from the fresh parse and `start=6960 end=6962 ... len=2` from the
cache hit. Line/col agree; the cache hit's byte offsets are the consistent ones, so the fresh
in-process bridge reads stale or placeholder offsets for some expression nodes that the dumped
pools carry correctly.

**Impact.** A warm build (cache hit, the default since 2026-10-25) and a cold build of the same
source produce different HIR spans: diagnostics positions and any span-keyed cache identity can
differ between cold and warm builds. Not caused by the node-storage lane (reproduces with only
`flat_ast_bridge` entrypoints), but it fixes the equality oracle of
`test/02_integration/compiler/data/ast_pool_snapshot_spec.spl`: the snapshot is compared to the
cache-hit restore, not to the fresh boxed tree.

**Repro.** In a spec: `flat_pool_capture_arm(); fresh = parse_and_build_module_scoped(src, path,
false); lines = flat_pool_capture_take(); hit = build_module_from_flat_pool_blob(lines, src,
path).unwrap()`, then compare `hir_module_encode(HirLowering.with_filename(path).lower_module(x))`
for `fresh` and `hit` line by line. Not fixed here (bridge owner).
