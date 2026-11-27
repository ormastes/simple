# Configured library mode independent source review — 2026-10-25

STATUS: WARN — NOT_RUN. Review cycle 2 source corrections accepted; no remaining P0/P1/P2 identified in the reviewed scope. Runtime and native admission remain pending.

Scope: the configuration candidate on HEAD `0caa93e3a83523aab301e8ecb1d024e2ccb0aa35` in `D:/dev/simple-smux-system-execution-20261025`, based on `b6e4922f1a318801a657c1e71ad5eb06666445f5`. The reviewer did not author the implementation. No compiler, interpreter, linker, runtime or SSpec process was launched. This report does not qualify Phase3, smux, runtime parity or a release. Unrelated owner files are excluded.

## Historical first-pass findings (resolved by cycle 2 below)

- **P1 — application selection can be overridden by an unrelated directory name.** `src/compiler/00.common/library_mode_policy_v1.spl:57` scans any `lib/<family>` segment as internal ownership. Source discovery passes a raw importer directory (`src/compiler/80.driver/driver_source_pipeline_loading.spl:1125`, `driver_preclosed_source_aliases.spl:54`, and the parent native closure), while alias identity uses the logical `SourceFile.module_name`. Reproducer by source trace: logical `app.entry` at `/project/lib/gc_sync_mut/entry.spl`, with configured `nogc-sync-mut`, imports `std.library_mode_probe`. Selection can choose the GC provider while registering its path under the NoGC scoped alias. No admitted standard-library owner binding proves the exception. Correction requested: carry one explicit, validated importer-owner context through physical selection and logical alias construction; arbitrary application directories must retain the configured family. Include both application-lookalike and genuine internal-owner cases.
- **P2 — replay mode verification compares two values derived from the same request.** `src/compiler/80.driver/cache/driver_hir_source_body_surfaces_v1.spl:60` compares the newly rebuilt registry mode with the option used to construct it at line 80, but does not compare the retained `streaming_module_surfaces_owner.library_mode`. `hir_cache_closure_digest` hashes physical declaration identities, excluding registry mode and import-route arrays. A changed mode with the same corpus can therefore pass this comparison. Correction requested: reject retained/requested mode mismatch before replay and independently compare both retained and replayed modes. A no-import corpus must demonstrate that refusal does not depend on incidental unresolved imports.

## Reviewed paths and limits

The first source pass traced public argv parsing and worker forwarding, typed options, closure publication/binding, source selection, preclosed aliases, frozen named/wildcard reexports, HIR missing-owner/export refusal, and source-body replay. It inspected request-owned mode arguments in options/no-op/prelower/MIR/weave/body custody and HIR key/header/parser-binding/load/store paths. The empty-mode conditional branches retain legacy framing, including requests with a nonempty legacy allowlist; configured mono recipes use v5 while empty-mode v1–v4 encoding branches retain their prior layout. These conclusions are code inspection, not executable byte-compatibility proof.

The 15 authored cases call production policy, resolver, parser/frozen registry, HIR/replay, cache I/O and codec functions. The eight native matrix rows specify distinct owner names and values, interleaved fresh/warm cache use, missing owner/export refusal, and explicit internal GC/async coexistence. All are NOT_RUN. Cache tests require actual private-cache admission and fail rather than silently skip when prerequisites are absent. The codec case directly exercises the simplest legacy envelope; broader v2–v4 compatibility remains source-reviewed and requires actual qualified execution. The identified replay guard and importer-authority defects must be corrected before this review can close.

## Historical first-freeze input pins

The following original 59-file manifest is retained verbatim as historical review input. Later fix-cycle pins must explicitly supersede changed entries; a current file must not be described by a historical hash.
Manifest SHA256: `bb9308634e99ca5b991765a40e920fd22470b1eed7b981a836ef8bee44365231`.
Patch SHA256: `d2d68b996457ae03f34a21e4601771438fc60470a3698f2ea4521502995156ea`.

# Configured library mode source freeze

Worktree: `D:/dev/simple-smux-system-execution-20261025`
HEAD: `0caa93e3a83523aab301e8ecb1d024e2ccb0aa35`
Initial config-edit baseline: `b6e4922f1a318801a657c1e71ad5eb06666445f5`; root advanced HEAD with the independent runner wrapper commit. Only this manifest is the configuration candidate.

Files: 59. All listed dirty files are this lane. No compiler/runtime execution. `git diff --check`: PASS (source whitespace only). No source validation/compiler helper launched.

## Review invariants

- New mode is an optional typed request field, never inferred from allowed_families, mutable process globals, environment policy, or a physical --source family root.
- Empty mode keeps legacy lookup order, policy digest bytes, HIR framing and mono recipe v1-v4 encoding unchanged. Configured-only v5 carries the body archive mode.
- Active argv transport covers coordinator, native and parse/fiber workers. Inactive NBO1 remains unchanged.
- Private scoped aliases distinguish application selection and explicit internal family, while preserving authored imports/defining identities. Frozen imports/reexports and body replay share request mode.
- HIR key/header/parser binding/load/store/has APIs accept optional default-empty mode; actual callers supply ctx.options.library_mode. Actual options/no-op/prelower/MIR/weave/body-custody identities bind nonempty mode.
- 15 authored executable cases, 0 executed. Eight native owner/value/cache/negative rows NOT_RUN. Source helper assertions are not native qualification.

## Exact manifest

| Path | SHA256 |
|---|---|
| `doc/03_plan/sys_test/configured_library_mode_native.md` | `61b6f1d90e721a46db0945f7b82abcff26424b05b39bf0f87b35497e5f759548` |
| `doc/06_spec/01_unit/compiler/library_mode_policy_v1_spec.md` | `b963933e9d80a1d0844005874c1e0d2c26cf0b925b428cf6e04b33a5ef8f64d2` |
| `doc/06_spec/02_integration/compiler/library_mode_cache_io_spec.md` | `9f1e397030a65b90ff531e2719936dba4c8e5f5d6ad81d8711fdecf5863aa7f6` |
| `doc/06_spec/02_integration/compiler/library_mode_frozen_surfaces_spec.md` | `a1326717f6254cca2a4f54e25ec92dbfa86f864a92e8426ab3851cf0e17058a5` |
| `doc/06_spec/02_integration/compiler/library_mode_selection_spec.md` | `3b1cdd1f4631dd52a601ab54d5f3d216d11989c51c26ff745a5d7eaf7ede6648` |
| `src/app/cli/native_build_main.spl` | `d95589808fa90af100ff1c68f040a787494092fc178efeac100cfd2d8a68d1e3` |
| `src/app/cli/native_build_output_plan.spl` | `f0b3a87f1b7e8496c26cd6e0fb7d425b9cc1ccac59482833ff2c9775c4128ed4` |
| `src/app/cli/native_build_parse_closure_owner.spl` | `4dfdf3e80f29985151f5d71a2ac20e6ee5fd417016ce32a79db70e1bb3113086` |
| `src/app/cli/parse_shard_main.spl` | `24cc07be9c9cca9383b5c23f4bd6f21a495007701647c244a9346345ebcc3663` |
| `src/app/io/_CliCompile/compile_targets.spl` | `b02c4b5dd762d9e489c4417b03c29d1fe0a0e4b9210054e3a0682a95be763835` |
| `src/app/io/_CliCompile/native_build_closure.spl` | `e568ee57145470424c202b252b743ac9d6c96493cc85ce9f6943469ec9dfb672` |
| `src/compiler/00.common/driver_compile_options.spl` | `1b6be6c23e2198e3f11c4fb98fa09d837cd86149a24d3943d67ed03482d6db7f` |
| `src/compiler/00.common/library_mode_policy_v1.spl` | `2f5747d5f2d5c8635a22a1999c5aa8560ba7ad9a5dd3dbaea29e6c0071b62a34` |
| `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl` | `c887039b164300dc223a37f5d3ad5eff18d1583fb2b8b1b749ee7385c8b8dd43` |
| `src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl` | `5c2c12eb30841e6852410e0772fcd9b0e734c4ab3b6a4ddba33fc21517157a1a` |
| `src/compiler/20.hir/hir_lowering/module_surface_export_index.spl` | `68ccb952016b7fe728a4751906b484eed04babeb40a3df984e18c9a3dc48fc10` |
| `src/compiler/20.hir/hir_lowering/module_surface_registry.spl` | `3a2994612a457be06eaed301265f8a42a81530738cd6b0219cc65a07ebd6b275` |
| `src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl` | `723162dfc343cab6792967b67a7e5ab722e22f51b52e0363f32e2ec46cd84eee` |
| `src/compiler/20.hir/hir_lowering/module_surface_types.spl` | `4247c0d6df04baa23177d79052d665cc0655ac8b2ff6911b9ed2c032711c2763` |
| `src/compiler/20.hir/hir_lowering/types.spl` | `c3af8554f170eea9cfd02380bc43991a9302ff68468bb97ee3c1c59807d1ba3c` |
| `src/compiler/80.driver/cache/compile_options_hash.spl` | `ccc7c6c69fcf3f1c8c5e77699316948d5be47b1f99911301624042afec1dc929` |
| `src/compiler/80.driver/cache/driver_hir_archive_authority_v1.spl` | `e1eb88afa2c7f1c56d6e39ac43af343727a63050657481a6d3b02130f6d6ee27` |
| `src/compiler/80.driver/cache/driver_hir_archive_weave_encoding_v1.spl` | `daf32d9cddb94a0a54295656f3b79900951ad9ed3e3e15298b54288d20ccabb7` |
| `src/compiler/80.driver/cache/driver_hir_managed_runtime_selection_v1.spl` | `73ebe5b8ee86dec583db694e79612afae26e3aba0a8db9cc2357d4137cfceca5` |
| `src/compiler/80.driver/cache/driver_hir_source_body_custody_identity_v1.spl` | `64fea5dbee9e67aeca88cfbbbf491b06f9ec91f19a7032c5fcd12bf6498de412` |
| `src/compiler/80.driver/cache/driver_hir_source_body_surfaces_v1.spl` | `62fe531f2b6c0e9d939b4ea0e3ddf74843f343216604c4ea39d877ec8403a019` |
| `src/compiler/80.driver/cache/hir_body_typecheck_lease_v1.spl` | `88317f6daf7987d8957541c82242e73e19a8cdb4157a66b513f3d2162c35158d` |
| `src/compiler/80.driver/cache/hir_mono_verification_recipe_codec_v1.spl` | `6b692f1a70dec7458ab5320bd8be863941eedb1736175d294f367a201a1bd3dd` |
| `src/compiler/80.driver/cache/native_noop_admission.spl` | `0317d857efe1b6d2688d3f9737a9d0994e20143992121421d685c4c2c2b2f332` |
| `src/compiler/80.driver/driver_hir_cache.spl` | `0d0ee20d47316eb649edf2301452ab54c3409f6ae1f6354559494a7f3f696ced` |
| `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` | `5c2aa1353c165ec02bdc4ff6d5979638b95ad5389616886805833b6e25344e15` |
| `src/compiler/80.driver/driver_library_mode_resolution_v1.spl` | `dcde0d95360ad605976196554d92d77b8c43cb9e07df684e8cdb164c98e60bf5` |
| `src/compiler/80.driver/driver_mir_selective_producer_v1.spl` | `d8469213c617abca2c5d6dc6e6bc1fd33185ef0dbcccfa4bddeec93bdb53e9b7` |
| `src/compiler/80.driver/driver_native_prelower_cache.spl` | `3e0d6bb212156d9c6558dbe218a257b58df21acb58cb0b0f884511b190d7516b` |
| `src/compiler/80.driver/driver_parse_shard_entry.spl` | `29fc58405be57e2a9b493b072d7db73dbe7380f1860150d202b6b9ccce8c4fac` |
| `src/compiler/80.driver/driver_preclosed_source_aliases.spl` | `962d0374b61af54d890b76024cc5b37282cbce56c0de7fc3eb7e60bdebbfbd61` |
| `src/compiler/80.driver/driver_source_pipeline_loading.spl` | `2cbcee44758b5c22c5e326fc82dc8e27231c13065b079f59acc7dd1a42983c08` |
| `src/compiler/80.driver/driver_source_pipeline_parsing.spl` | `2a5cd6d467587559b00a68b74d6985cc22ddb26ed89cffd464bfd72b995622e2` |
| `src/compiler/80.driver/driver_types.spl` | `cbefc9d095bda28c6d7ab1099cea18e7cfb29b5b8a53dd46258a9477428844d2` |
| `test/01_unit/compiler/library_mode_policy_v1_spec.spl` | `fad29cf76359a134952e86f802fb218547f334a658032bcabd0d7cdbe776efaa` |
| `test/02_integration/compiler/library_mode_cache_io_spec.spl` | `bcee28d3276c84b493cd36221bdb9b9bc55af941c9af32a6bf56c222ac8064ef` |
| `test/02_integration/compiler/library_mode_frozen_surfaces_spec.spl` | `d76e7ae1843c99052bdd7d0ab4b2f908266b34c07c10685b80a451914462767b` |
| `test/02_integration/compiler/library_mode_selection_spec.spl` | `4eec830ec35a6b602a9ca68c8180200567855cd1956142939341c230b94b5f2b` |
| `test/fixtures/compiler/library_mode_selection/README.md` | `3820059266e8046b6ff24eeb2fe2467e9484434d0ab371d8f4392b03811c0bc2` |
| `test/fixtures/compiler/library_mode_selection/entry.spl` | `2d453f186ffb2c19bb5d1f91d41709bc9de88f624a4b1db361624ecadb431618` |
| `test/fixtures/compiler/library_mode_selection/internal_entry.spl` | `94e0670c7627af3004831407bafff2c9fbc0bceee8dce8757293cd894d08a4b7` |
| `test/fixtures/compiler/library_mode_selection/lib/common/library_named_reexport.spl` | `40357df40b80f4e491a72c01b56997e1ab2cdb19f764184de4beba7d6f1da0e2` |
| `test/fixtures/compiler/library_mode_selection/lib/common/library_reexport.spl` | `6d11df76d174b5ff60b41ca22690f3c05c60aba1d6dcee6da26a3e9ce9848412` |
| `test/fixtures/compiler/library_mode_selection/lib/common/library_shared_probe.spl` | `5b80db1db96aa99ff4bcbdc108b0adbc360b5d0a35f273830c3cf879187f8512` |
| `test/fixtures/compiler/library_mode_selection/lib/gc_sync_mut/library_internal.spl` | `0cebd7e1992a2b0e2e27f54303a00e53fe85a2faea04c788bff3fa47c2a202d1` |
| `test/fixtures/compiler/library_mode_selection/lib/gc_sync_mut/library_mode_probe.spl` | `837d17500a964e4f9e02d1e5cb51237ec14fe8c09ed0ffa0d13d903644f02467` |
| `test/fixtures/compiler/library_mode_selection/lib/nogc_async_mut/library_async_only.spl` | `08869049190029d5f3fb5f10cebb6160d2c06a7c89b2cd5fa0adb4dc9722006f` |
| `test/fixtures/compiler/library_mode_selection/lib/nogc_async_mut/library_internal.spl` | `252506be96458908b5a96d403bc4fe026c3bc3d93f940547ea16a176e13bfcd6` |
| `test/fixtures/compiler/library_mode_selection/lib/nogc_async_mut/library_mode_probe.spl` | `2948478688c714933d46ee3d98ba784e9f5aae01a5b838253b131346d7081523` |
| `test/fixtures/compiler/library_mode_selection/lib/nogc_async_mut/library_symbol_collision.spl` | `20970c02ea312080b73e6a1f326466f64f5325855ddbe0d62f13207e118da013` |
| `test/fixtures/compiler/library_mode_selection/lib/nogc_sync_mut/library_mode_probe.spl` | `574159f505f5128bcdbac31d90a0b2c3c72ac0481aca0a89b19ca55c50e3b08d` |
| `test/fixtures/compiler/library_mode_selection/missing_owner.spl` | `9f1818a8799ed6b9475bf71de649699f354b39f725eef815ec8e339e8bd15541` |
| `test/fixtures/compiler/library_mode_selection/missing_symbol.spl` | `5d908a1fe61d8f0384a3c6b0d2e5490fdb3a7f11994406dbc4254ca287f9d5e2` |
| `test/fixtures/compiler/library_mode_selection/mixed_entry.spl` | `9473bac4ec23f57a16d9d9ff5e766ae391628e4a9e29e539c754d93085e612aa` |

## Cycle 2 independent disposition

The frozen correction delta was reviewed against the historical cycle-1 findings. HEAD remains `0caa93e3a83523aab301e8ecb1d024e2ccb0aa35`; this review identifies the uncommitted candidate by exact file hashes below, not by HEAD alone. All entries in the v2 manifest were checked against current bytes and matched. The unchanged 34-owner implementation was not rerun through a second broad review, and no previous green check was repeated.

**P1 resolved by source inspection.** `library_mode_importer_context_valid_v1` rejects raw paths and private scoped coordinates. Internal-family recognition accepts only a leading `std.<family>` or `lib.<family>` logical namespace, not a substring or ancestor. Configured resolver APIs take `importer_owner` separately from the physical importer used for relative/legacy lookup. The parent closure supplies `driver_closure_importer_module_v1`; ordinary and preclosed walks supply the retained `SourceFile.module_name` also used to derive their scoped alias. Frozen/export resolution uses the retained surface module name, and HIR uses the retained importer surface owner. Empty mode keeps the old filesystem lookup path. The new real fixture beneath `lib/gc_sync_mut/project/src/app` derives `app.ancestor_entry`, checks the NoGC provider through the production resolver, verifies the preclosed scoped alias maps to that provider, and refuses missing/path-valued owner context. Existing explicit internal GC/async controls remain. The regression is authored, not executed.

**P2 resolved by source inspection.** `driver_hir_source_body_replay_surfaces_v1` compares the retained registry mode with the requested mode before rebuilding or opening scratch; disagreement returns `LIBRARY_MODE_REPLAY_MISMATCH`. Final verification compares rebuilt, requested and retained modes. The added no-import corpus first exercises unchanged-mode replay, then changes only the requested mode and requires that exact diagnostic, while checking the retained mode remains unchanged. Missing dependencies cannot explain this negative control. It is authored, not executed.

The canonical native CLI help row now advertises the semantic flag. The root-owned guide distinguishes semantic library selection from runtime-tier policy, preserves legacy allowlists when mode is absent, prohibits physical-family pinning as configuration, and explicitly requires native owner/value/cache qualification. Fixture relocation to canonical `src/app` and `src/lib` namespaces gives actual collector identities to the regression; the plan includes the hostile-ancestor native row.

No remaining P0/P1/P2 was identified in the reviewed correction delta. This closes the two source findings only. **17 authored specifications and nine native matrix rows remain NOT_RUN; zero execution passes are claimed.** Compiler checking, actual fresh/warm cache behavior, stage parity, core/MCP smoke and smux system execution remain separate pending gates. This report is not a production PASS or release admission.

### Current cycle-2 pins

The v1 manifest above is historical. The following v2 manifest supersedes its changed or relocated entries; unchanged entries retain their original hashes. Root's guide is separately pinned because it is outside the author's manifest. The reviewer owns only this report.
V2 manifest SHA256: `f6ff6666d63467bb78e618dc4d929265e7b3c28734115357866337af395f6ebf`.
Root guide `doc/07_guide/compiler/configured_variants_and_aggregate_validation.md` SHA256: `77e46508d61f69f759adb1003b6658c4bf9611305fd807448cc40f127e6b8c46`.

## Current exact owned manifest

| Path | SHA256 |
|---|---|
| `doc/03_plan/sys_test/configured_library_mode_native.md` | `d28a9fd4b38452d4964e4054056718fabdf130e11da07e9d7e4e05cd650eeff3` |
| `doc/06_spec/01_unit/compiler/library_mode_policy_v1_spec.md` | `b963933e9d80a1d0844005874c1e0d2c26cf0b925b428cf6e04b33a5ef8f64d2` |
| `doc/06_spec/02_integration/compiler/library_mode_cache_io_spec.md` | `9f1e397030a65b90ff531e2719936dba4c8e5f5d6ad81d8711fdecf5863aa7f6` |
| `doc/06_spec/02_integration/compiler/library_mode_frozen_surfaces_spec.md` | `f5742fd8debcd92804c96e23cc7aad1afab0e2d7d2f93dee56ec5764a84d0479` |
| `doc/06_spec/02_integration/compiler/library_mode_selection_spec.md` | `7d9aaa6a4b9ce94efff64aa999a6397d136915ba9f873400b775415da9c85b24` |
| `src/app/cli/native_build_main.spl` | `4f9dc583f08219a0c02ea99e68be7d74933982357bd1c5290211450805531087` |
| `src/app/cli/native_build_output_plan.spl` | `f0b3a87f1b7e8496c26cd6e0fb7d425b9cc1ccac59482833ff2c9775c4128ed4` |
| `src/app/cli/native_build_parse_closure_owner.spl` | `4dfdf3e80f29985151f5d71a2ac20e6ee5fd417016ce32a79db70e1bb3113086` |
| `src/app/cli/parse_shard_main.spl` | `24cc07be9c9cca9383b5c23f4bd6f21a495007701647c244a9346345ebcc3663` |
| `src/app/io/_CliCompile/compile_targets.spl` | `b02c4b5dd762d9e489c4417b03c29d1fe0a0e4b9210054e3a0682a95be763835` |
| `src/app/io/_CliCompile/native_build_closure.spl` | `04210a6c194e88ea7b48e0082f3977963a4dde60e10d6edd9d6f58090c0b7d62` |
| `src/compiler/00.common/driver_compile_options.spl` | `1b6be6c23e2198e3f11c4fb98fa09d837cd86149a24d3943d67ed03482d6db7f` |
| `src/compiler/00.common/library_mode_policy_v1.spl` | `8d254fc19cc407f99d8c74fe576b53eb9a020d1647033586acdc6de5c0202849` |
| `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl` | `c887039b164300dc223a37f5d3ad5eff18d1583fb2b8b1b749ee7385c8b8dd43` |
| `src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl` | `a057cb2577555ff860aafa727d938de2a747021cc37177d2faf648bc528f6056` |
| `src/compiler/20.hir/hir_lowering/module_surface_export_index.spl` | `91ce6a67ce79d3a1335d7649380c1839e51a23d336808a173badc8f1cd2bbe2d` |
| `src/compiler/20.hir/hir_lowering/module_surface_registry.spl` | `3a2994612a457be06eaed301265f8a42a81530738cd6b0219cc65a07ebd6b275` |
| `src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl` | `f744d066e9dfea5424a1127542539d8b9cfa5b4b56367d62fcb42250d64dbb0c` |
| `src/compiler/20.hir/hir_lowering/module_surface_types.spl` | `4247c0d6df04baa23177d79052d665cc0655ac8b2ff6911b9ed2c032711c2763` |
| `src/compiler/20.hir/hir_lowering/types.spl` | `c3af8554f170eea9cfd02380bc43991a9302ff68468bb97ee3c1c59807d1ba3c` |
| `src/compiler/80.driver/cache/compile_options_hash.spl` | `ccc7c6c69fcf3f1c8c5e77699316948d5be47b1f99911301624042afec1dc929` |
| `src/compiler/80.driver/cache/driver_hir_archive_authority_v1.spl` | `e1eb88afa2c7f1c56d6e39ac43af343727a63050657481a6d3b02130f6d6ee27` |
| `src/compiler/80.driver/cache/driver_hir_archive_weave_encoding_v1.spl` | `daf32d9cddb94a0a54295656f3b79900951ad9ed3e3e15298b54288d20ccabb7` |
| `src/compiler/80.driver/cache/driver_hir_managed_runtime_selection_v1.spl` | `73ebe5b8ee86dec583db694e79612afae26e3aba0a8db9cc2357d4137cfceca5` |
| `src/compiler/80.driver/cache/driver_hir_source_body_custody_identity_v1.spl` | `64fea5dbee9e67aeca88cfbbbf491b06f9ec91f19a7032c5fcd12bf6498de412` |
| `src/compiler/80.driver/cache/driver_hir_source_body_surfaces_v1.spl` | `c22cb8bfd2551f63d50fc60ccea4179a0b9ba487c5bf6dfb510e105045df543c` |
| `src/compiler/80.driver/cache/hir_body_typecheck_lease_v1.spl` | `88317f6daf7987d8957541c82242e73e19a8cdb4157a66b513f3d2162c35158d` |
| `src/compiler/80.driver/cache/hir_mono_verification_recipe_codec_v1.spl` | `6b692f1a70dec7458ab5320bd8be863941eedb1736175d294f367a201a1bd3dd` |
| `src/compiler/80.driver/cache/native_noop_admission.spl` | `0317d857efe1b6d2688d3f9737a9d0994e20143992121421d685c4c2c2b2f332` |
| `src/compiler/80.driver/driver_hir_cache.spl` | `0d0ee20d47316eb649edf2301452ab54c3409f6ae1f6354559494a7f3f696ced` |
| `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` | `5c2aa1353c165ec02bdc4ff6d5979638b95ad5389616886805833b6e25344e15` |
| `src/compiler/80.driver/driver_library_mode_resolution_v1.spl` | `dbf7f97fd484794e821bfb1515212f5c10024e21d83b9602d9e9927c52fb1633` |
| `src/compiler/80.driver/driver_mir_selective_producer_v1.spl` | `d8469213c617abca2c5d6dc6e6bc1fd33185ef0dbcccfa4bddeec93bdb53e9b7` |
| `src/compiler/80.driver/driver_native_prelower_cache.spl` | `3e0d6bb212156d9c6558dbe218a257b58df21acb58cb0b0f884511b190d7516b` |
| `src/compiler/80.driver/driver_parse_shard_entry.spl` | `29fc58405be57e2a9b493b072d7db73dbe7380f1860150d202b6b9ccce8c4fac` |
| `src/compiler/80.driver/driver_preclosed_source_aliases.spl` | `1401e85718049ff95feb592e4f1308ffa121d81aebeaf37c3c9da577be764242` |
| `src/compiler/80.driver/driver_source_pipeline_loading.spl` | `3760b1b70049d3f8fbb39b91cc46e9fdea6c193621b5200b6138457f498ecadf` |
| `src/compiler/80.driver/driver_source_pipeline_parsing.spl` | `2a5cd6d467587559b00a68b74d6985cc22ddb26ed89cffd464bfd72b995622e2` |
| `src/compiler/80.driver/driver_types.spl` | `cbefc9d095bda28c6d7ab1099cea18e7cfb29b5b8a53dd46258a9477428844d2` |
| `test/01_unit/compiler/library_mode_policy_v1_spec.spl` | `ee67f836013fe63ffcd5f8548b22e3f2c00e8148fea085b58e9a7c3e0d1b2018` |
| `test/02_integration/compiler/library_mode_cache_io_spec.spl` | `8fc5399c1eb182a2d34c2015d56343962fe2305bd60791deaabc708663707018` |
| `test/02_integration/compiler/library_mode_frozen_surfaces_spec.spl` | `90628d17ebb2ac7784c011e7f324ce2cef70b941768f09caa8586cf15e34d9c5` |
| `test/02_integration/compiler/library_mode_selection_spec.spl` | `ca9535e4061f127ae7e020956a6a04ecba002b5e0af5a25d1c4d2c212cbd6169` |
| `test/fixtures/compiler/library_mode_selection/README.md` | `bc955c5d2dba3f3c0de77cf4a9a677181154b6ac77c26b4be8feaf48e0ccbc19` |
| `test/fixtures/compiler/library_mode_selection/lib/gc_sync_mut/project/src/app/ancestor_entry.spl` | `e1dc1979d3da56f55c1485ff5562c2fcb070f9590172c12db902055e3270b143` |
| `test/fixtures/compiler/library_mode_selection/src/app/entry.spl` | `2d453f186ffb2c19bb5d1f91d41709bc9de88f624a4b1db361624ecadb431618` |
| `test/fixtures/compiler/library_mode_selection/src/app/internal_entry.spl` | `94e0670c7627af3004831407bafff2c9fbc0bceee8dce8757293cd894d08a4b7` |
| `test/fixtures/compiler/library_mode_selection/src/app/missing_owner.spl` | `9f1818a8799ed6b9475bf71de649699f354b39f725eef815ec8e339e8bd15541` |
| `test/fixtures/compiler/library_mode_selection/src/app/missing_symbol.spl` | `5d908a1fe61d8f0384a3c6b0d2e5490fdb3a7f11994406dbc4254ca287f9d5e2` |
| `test/fixtures/compiler/library_mode_selection/src/app/mixed_entry.spl` | `9473bac4ec23f57a16d9d9ff5e766ae391628e4a9e29e539c754d93085e612aa` |
| `test/fixtures/compiler/library_mode_selection/src/app/no_imports.spl` | `67bcadde896ecf50cfe4a13f094ce5fa59398c6f1d91df114c83db705af5e950` |
| `test/fixtures/compiler/library_mode_selection/src/lib/common/library_named_reexport.spl` | `40357df40b80f4e491a72c01b56997e1ab2cdb19f764184de4beba7d6f1da0e2` |
| `test/fixtures/compiler/library_mode_selection/src/lib/common/library_reexport.spl` | `6d11df76d174b5ff60b41ca22690f3c05c60aba1d6dcee6da26a3e9ce9848412` |
| `test/fixtures/compiler/library_mode_selection/src/lib/common/library_shared_probe.spl` | `5b80db1db96aa99ff4bcbdc108b0adbc360b5d0a35f273830c3cf879187f8512` |
| `test/fixtures/compiler/library_mode_selection/src/lib/gc_sync_mut/library_internal.spl` | `0cebd7e1992a2b0e2e27f54303a00e53fe85a2faea04c788bff3fa47c2a202d1` |
| `test/fixtures/compiler/library_mode_selection/src/lib/gc_sync_mut/library_mode_probe.spl` | `837d17500a964e4f9e02d1e5cb51237ec14fe8c09ed0ffa0d13d903644f02467` |
| `test/fixtures/compiler/library_mode_selection/src/lib/nogc_async_mut/library_async_only.spl` | `08869049190029d5f3fb5f10cebb6160d2c06a7c89b2cd5fa0adb4dc9722006f` |
| `test/fixtures/compiler/library_mode_selection/src/lib/nogc_async_mut/library_internal.spl` | `252506be96458908b5a96d403bc4fe026c3bc3d93f940547ea16a176e13bfcd6` |
| `test/fixtures/compiler/library_mode_selection/src/lib/nogc_async_mut/library_mode_probe.spl` | `2948478688c714933d46ee3d98ba784e9f5aae01a5b838253b131346d7081523` |
| `test/fixtures/compiler/library_mode_selection/src/lib/nogc_async_mut/library_symbol_collision.spl` | `20970c02ea312080b73e6a1f326466f64f5325855ddbe0d62f13207e118da013` |
| `test/fixtures/compiler/library_mode_selection/src/lib/nogc_sync_mut/library_mode_probe.spl` | `574159f505f5128bcdbac31d90a0b2c3c72ac0481aca0a89b19ca55c50e3b08d` |
