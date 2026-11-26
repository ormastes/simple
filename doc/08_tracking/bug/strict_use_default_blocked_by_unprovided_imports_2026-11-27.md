# Strict braced-`use` default is blocked by unprovided imports (2026-11-27)

**Status:** open
**Area:** stdlib and specs; seed loader `SIMPLE_STRICT_USE`

## Symptom
Since PR #12067, `use m.{x}` where `m` does not itself provide `x` gives a `[use-warning]` by default. With `SIMPLE_STRICT_USE=1` it is a hard error. The default cannot flip to strict while the tree still has these sites.

## Fixed so far
The first census found 6 sites. PR work/strict-use-census-sites-20261127 fixed 5 of them:
- `PureDatabase` and `PureDatabaseBitmapReducerV1`: now exported from the facade.
- `env_get_opt`, `dir_exists`: importers moved to the owner.
- `should_rewrite`, `rewrite_elementwise_add_guarded`: the exports were corrected.

## Open
- **Undefined constants:** `SYM_OS_CRC32_UPDATE_BYTE`, `_U32` and `_U64` are defined nowhere. `test/01_unit/compiler/mir_opt/cipher/cipher_parity_spec.spl` imports them from `compiler.mir_opt.pattern.rules_crypto`. Add the constants or drop them from the spec.
- **Wider census:** strict `test` over `test/01_unit/lib`, seed `simple-local-20261127e`. The list below is a lower bound, for two reasons:
  - strict mode stops at the first error in each spec, so later sites are masked;
  - the database, common, crypto, gc_async_mut, nogc_async_mut, nogc_sync_mut, orchestration, scv and skia directories timed out at 1500s.

Columns: distinct importers, symbol, via-module.

```
3	PersistentVec	std.gc_async_immut.{...}
2	Atom	std.gc_async_immut.{...}
2	cpu_simd_required_evidence_valid	std.gpu.engine2d.simd_kernels.{...}
2	env_get_or	std.io_runtime.{...}
2	pmap	std.gc_async_immut.{...}
2	simd_blit_rect	std.gpu.engine2d.simd_kernels.{...}
1	AssetBundle	std.nogc_sync_mut.engine.build.build_config.{...}
1	Atom	std.gc_sync_immut.{...}
1	DbRow	std.db.db_persistence.{...}
1	DbValue	std.database.pure_sql.{...}
1	DbfsFsDriver	nogc_async_mut.db.dbfs_engine.{...}
1	DescriptorTable	std.nogc_async_mut.gpu.object_vm.{...}
1	EvidenceBoundI64ManifestV1	std.sffi.sffi_signature.{...}
1	FfiManifest	std.sffi.sffi_signature.{...}
1	FixedVec	std.simd.{...}
1	GpuCasStore	std.nogc_async_mut.gpu.store.{...}
1	HTTP1_REQUEST_LINE_MAX_BYTES	std.nogc_async_mut.http_server.parser.{...}
1	NVFS_STREAM_INGEST_PROVIDER_V1	std.fs_driver.nvfs_driver.{...}
1	PersistentList	std.gc_async_immut.{...}
1	PersistentList	std.gc_sync_immut.{...}
1	PersistentMap	std.gc_async_immut.{...}
1	PersistentMap	std.gc_sync_immut.{...}
1	PersistentSet	std.gc_async_immut.{...}
1	PersistentSet	std.gc_sync_immut.{...}
1	PersistentTrie	std.gc_async_immut.{...}
1	PersistentTrie	std.gc_sync_immut.{...}
1	PersistentVec	std.gc_sync_immut.{...}
1	PropertyTrees	std.cc.entity.property_tree.{...}
1	RunRecord	std.test_runner.test_db_types.{...}
1	TINY_KEY_DOWN	std.tiny.gui.state.{...}
1	TextBlitCache	std.gpu.engine2d.helpers_text.{...}
1	Vector	std.simd.{...}
1	VersionedSnapshot	std.gc_async_immut.{...}
1	_execute_it	std.spec.{...}
1	_forced_simd_level	std.gpu.engine2d.simd_kernels.{...}
1	_scalar_fill_row	std.gpu.engine2d.simd_kernels.{...}
1	build_gcm_explicit_nonce_hex	std.http_server.worker.{...}
1	bytes_to_text	std.common.base_encoding.utilities.{...}
1	bytes_to_text	std.common.cbor.types.{...}
1	chacha20_keystream	std.crypto.chacha20.{...}
1	channel_send_by_id	std.concurrent.channel.{...}
1	compile_to_vhdl_module	lib.hardware.fpga_linux.riscv_fpga_linux.{...}
1	create_slide_from_layout_id	app.office.slides.slide.{...}
1	default_rate_limit_config	std.http_server.rate_limit.{...}
1	default_security_headers_config	std.http_server.security_headers.{...}
1	describe	std.testing.{...}
1	edition_values_from_policy	std.test_runner.test_runner_config.{...}
1	extract_spl_blocks_from_content	std.test_runner.sdoctest.extractor.{...}
1	fe_pow	std.common.math.field.fe_p256.{...}
1	generate_k26_soc_top_vexriscv	lib.hardware.fpga_k26.k26_soc_top.{...}
1	metal_sffi_quarantine_release_proven	std.gc_async_mut.io.metal_sffi.{...}
1	normalize_profile_name	std.test_runner.test_runner_args.{...}
1	null_block_status_ready	std.driver.null_block_driver.{...}
1	parse_signed_nth_length	std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer_foundation_values.{...}
1	posting_list_new	std.db.accel.{...}
1	pure_database_changes	std.database.pure_sql.{...}
1	remote_security_token_payload_v2	std.security.types.{...}
1	roots	std.common.storage_roots.contracts.{...}
1	rt_file_read_bytes	std.nogc_sync_mut.ffi.io.{...}
1	rt_vulkan_init	std.nogc_sync_mut.io.vulkan_sffi.{...}
1	scalablevec_splat	std.simd.{...}
1	self_tree_rss_mb	std.test_runner.system_monitor.{...}
1	simd_isa_copy_span	std.nogc_sync_mut.gpu.engine2d.simd_isa_provider.{...}
1	simd_scroll_region	std.gpu.engine2d.simd_kernels.{...}
1	sqlite_handle_valid	std.io.sqlite_sffi.{...}
1	synthesis_project_default	lib.hardware.fpga_linux.synthesis_wrapper.{...}
1	text_to_bytes	std.common.base_encoding.utilities.{...}
1	try_compress_bytes	std.common.compress.{...}
1	validate_csrf_token	std.http_server.csrf.{...}
1	validate_request_path	std.http_server.request_validation.{...}
```

## Fix direction
For each site, import from the defining module, or add an explicit `export` when the middle module really is the public facade. Flip the default once a full census, including the timed-out directories, is empty.
