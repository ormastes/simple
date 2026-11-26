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

Batch 2 (work/strict-use-census-batch2-20261127) fixed 50 of the 70 wider-census rows (plus the names each fix unmasked); the 20 left are below, with 2 newly unmasked rows:
- Facade exports added (`test_runner_args` `normalize_profile_name`, `app.io.cli_commands` `_run_normalize_profile_name`, async-family and `gc_*_immut` facades that lagged their owners): `gc_async_immut`, `gc_sync_immut`, `std.io_runtime`, `nogc_async_mut` `simd_kernels`, `sffi_signature`, `db.accel`, `security.types`, `test_runner.{test_runner_config,system_monitor,sdoctest.extractor,sdoctest.discovery}`, `io.{sqlite_sffi,metal_sffi}`, `driver.null_block_driver`, `concurrent.channel`, `spec`, `database.pure_sql` (both families), `common.compress`, `nogc_sync_mut.engine.build.build_config`.
- Importers repointed to the owner: simd specs (`std.simd.{fixed,scalable,scalable_adapter,vector}`), `TINY_KEY_*` (`tiny.gui.event_dispatch`), `describe` (`std.spec`), `DbValue` (`database.sql.types`), `bytes_to_text`/`text_to_bytes` (the `base_encoding_*` / `cbor_*` owner names via `as`), `RunRecord` -> `TrdRunRecord`.
- Stale names removed: `roots` (a doc-comment example leaked into `storage_roots/__init__`), `DbfsFsDriver` is a different type from `DbFsDriver`; `nogc_async_mut/db/__init__` named it from `dbfs_engine`, which does not provide it, so it now exports it from `dbfs_engine.fs_driver` (gc_async_mut and gc_sync_mut db facades resolve through it), unused `DbRow` import, unused `bytes_to_text` import in `os/userlib/_Window/client_methods`, `parse_signed_nth_length` -> `parse_signed_nth_length_milli` (rename left stale exports).

## Open
- **Undefined constants:** `SYM_OS_CRC32_UPDATE_BYTE`, `_U32` and `_U64` are defined nowhere. `test/01_unit/compiler/mir_opt/cipher/cipher_parity_spec.spl` imports them from `compiler.mir_opt.pattern.rules_crypto`. Add the constants or drop them from the spec.
- **Wider census:** strict `test` over `test/01_unit/lib`, seed `simple-local-20261127e`. The list below is a lower bound, for two reasons:
  - strict mode stops at the first error in each spec, so later sites are masked;
  - the database, common, crypto, gc_async_mut, nogc_async_mut, nogc_sync_mut, orchestration, scv and skia directories timed out at 1500s.

Columns: distinct importers, symbol, via-module, reason it is still open.

```
1	DescriptorTable	std.nogc_async_mut.gpu.object_vm.{...}	undefined: class folded into the object_vm oracle fns (descriptor_table.spl:29); spec stale
1	GpuCasStore	std.nogc_async_mut.gpu.store.{...}	undefined: only CasStore exists, API differs; spec stale
1	HTTP1_REQUEST_LINE_MAX_BYTES	std.nogc_async_mut.http_server.parser.{...}	undefined anywhere
1	NVFS_STREAM_INGEST_PROVIDER_V1	std.fs_driver.nvfs_driver.{...}	undefined anywhere (3 specs name it)
1	PropertyTrees	std.cc.entity.property_tree.{...}	cc module has no PropertyTrees/property_trees_new/ScrollNode; only an unrelated render_opt.PropertyTrees class exists, not rebound
1	TextBlitCache	std.gpu.engine2d.helpers_text.{...}	undefined anywhere
1	build_gcm_explicit_nonce_hex	std.http_server.worker.{...}	undefined anywhere
1	chacha20_keystream	std.crypto.chacha20.{...}	undefined anywhere (dead_braced_import_reported_spec names it on purpose)
1	compile_to_vhdl_module	lib.hardware.fpga_linux.riscv_fpga_linux.{...}	undefined (comment mention only)
1	create_slide_from_layout_id	app.office.slides.slide.{...}	undefined (comment mention only)
1	default_rate_limit_config	std.http_server.rate_limit.{...}	undefined anywhere
1	default_security_headers_config	std.http_server.security_headers.{...}	undefined anywhere
1	fe_pow	std.common.math.field.fe_p256.{...}	undefined anywhere
1	generate_k26_soc_top_vexriscv	lib.hardware.fpga_k26.k26_soc_top.{...}	undefined anywhere
1	rt_file_read_bytes	std.nogc_sync_mut.ffi.io.{...}	skipped: only scattered per-file extern decls, no owner module; importer test/03_system/os/os_crypto_ref_helpers.spl actually imports sffi.io
1	rt_vulkan_init	std.nogc_sync_mut.io.vulkan_sffi.{...}	skipped: io.vulkan_sffi and gpu.engine2d.sffi_vulkan import each other and the ownership spec pins that layout
1	simd_isa_copy_span	std.nogc_sync_mut.gpu.engine2d.simd_isa_provider.{...}	undefined anywhere
1	synthesis_project_default	lib.hardware.fpga_linux.synthesis_wrapper.{...}	undefined anywhere
1	validate_csrf_token	std.http_server.csrf.{...}	undefined anywhere
1	validate_request_path	std.http_server.request_validation.{...}	undefined anywhere
1	hal_smp_ipi_window	os.kernel.arch.riscv64.hal_smp.{...}	newly unmasked, undefined (riscv_noalloc_dtb_capability_spec)
1	simple_web_layout_last_render_degraded	std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{...}	newly unmasked (before_after_generated_content_chrome159_spec), not triaged
```

## Fix direction
For each site, import from the defining module, or add an explicit `export` when the middle module really is the public facade. Flip the default once a full census, including the timed-out directories, is empty.
