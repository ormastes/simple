# Strict braced-`use` default is blocked by unprovided imports (2026-11-27)

**Status:** open (7 rows left after batch 4)
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
- (fixed in batch 4) `SYM_OS_CRC32_UPDATE_*`: the `os_crc32` rules were removed when SimpleOS and std shared one CRC32 (G3 C2/C4); the spec entries were dead and are dropped.
- **Wider census:** strict `test` over `test/01_unit/lib`, seed `simple-local-20261127e`. The list below is a lower bound, for two reasons:
  - strict mode stops at the first error in each spec, so later sites are masked;
  - the database, common, crypto, gc_async_mut, nogc_async_mut, nogc_sync_mut, orchestration, scv and skia directories timed out at 1500s.

Batch 3 (work/strict-use-census-batch3-20261127) fixed 4 of the 22 rows (plus names each fix unmasked); the rest are below, each re-checked as USED in its importer, so deleting the import would break the spec and the symbol exists nowhere (never stubbed):
- `compile_to_vhdl_module` (`soc_vhdl_gen_rv64_spec`), `synthesis_project_default` plus unmasked `add_verilog_sources`, `enable_axi_hp_port`, `SynthesisProject` (`synthesis_wrapper_vexriscv_spec`; the block also duplicated an existing `generate_vivado_tcl_rv64` import): unused imports deleted. That spec now loads and runs 16 examples; 5 fail on assertions that the import error had masked (separate pre-existing failures, not touched here).
- `chacha20_keystream`: unused in `chacha20_spec`, removed from that import. `dead_braced_import_reported_spec` keeps naming it on purpose (fixture text).
- `simple_web_layout_last_render_degraded` (+ `_degrade_reason`): the renderer facade now `export use`s them from `..._renderer_foundation`. Unmasked `_scalar_fill_row`: `gc_async_mut.gpu.engine2d.simd_kernels` facade lagged its owner, now exports it.

Batch 4 (work/strict-use-census-4-20261127) fixed 11 of the 18 rows plus `SYM_OS_CRC32_UPDATE_*` and 3 unmasked names; 7 rows remain, each a whole missing feature:
- `default_rate_limit_config`/`new_rate_limit_store`/`check_rate_limit` (rate_limit_spec), `validate_csrf_token`/`is_csrf_exempt_method`/`default_csrf_config` (csrf_spec), `default_security_headers_config`/`build_security_header_value` (security_headers_spec), `validate_request_path`/`validate_uri_length`/`default_max_uri_length` (request_validation_spec): phantom API; the specs now use the real classes (`X.default()`, `rate_limit_handler`, `request_validation_handler`, `constant_time_eq`, `build_hsts_value`). Two phantom zero-arg `generate_csrf_token` examples were deleted (they cannot run: the real call needs a secret and the HMAC extern). Specs now run 7/7, 12/12, 32/32, 6/6 (they executed 0 before).
- `fe_pow` + unmasked `fe_cond_swap`: implemented in `common/math/field/fe_p256.spl` (big-endian exponent bytes; `fe_cond_swap` is constant time). `fe_p256_full_spec`: 53/55; the 2 failures are pre-existing and were masked: `fe_to_bytes(p)` / `fe_is_zero(p)` do not reduce the non-canonical zero p.
- `create_slide_from_layout_id`: implemented in `app/office/slides/slide.spl` (registry-driven, activates the extension first); slides_layout_registry_spec 11/11, office_readers_activate_before_read_spec 2/2.
- `hal_smp_ipi_window`, `hal_smp_hsm_target`: implemented in `os/kernel/arch/riscv64/hal_smp.spl` (sparse hart IDs above 63) and now used by `hal_smp_cpu_start` / `hal_smp_ipi_send`; the dtb-capability accessors are exported. Both examples pass; 2 other examples in that spec (NUL-terminated ISA, handoff source order) fail and were masked (pre-existing). `hal_smp_ipi_broadcast` still sends one window-0 mask (sparse harts above 63 are not addressed there).
- `simd_isa_copy_span`: implemented in `simd_isa_provider.spl`, wired into `simd_span_batch_execute`; unmasked `_kernel_probe_copy_bucket` implemented in `backend_software.spl` and COPY_SPAN is now probe-registered per size bucket like the other ops. dispatch spec 11/11.
- `HTTP1_REQUEST_LINE_MAX_BYTES`: spec repointed to `http_core.MAX_REQUEST_LINE`; unmasked `http1_header_name_is_token` extracted from `parse_header_line` and exported; the partial request-line bound is now exact (max+1 bytes is allowed only when the last byte is CR). request_framing_strict_spec 4/4.
- `rt_vulkan_init` (+ 10 sibling names): `vulkan_backend3d` imported them from `io.vulkan_sffi`, which only imports them from `gpu.engine2d.sffi_vulkan`; they now come from `sffi_vulkan` (layout pinned by the ownership spec is untouched). The spec still has 2 pre-existing failures (`make_bind_font_texture_cmd`, `make_draw_cmd` not found).
- `rt_file_read_bytes`: `os_crypto_ref_helpers` declares its two externs locally (the repo pattern; `sffi.io` never owned them).
- Unmasked and fixed: `file_read_text` via `std.io_runtime` (riscv64_kernel_closure_hygiene_spec -> `io.file_ops`), `simple_web_layout_uses_legacy_widget_chrome` (renderer facade now re-exports it from the foundation).

Rows left (all re-checked, symbol exists nowhere, spec is the only caller):
```
1	DescriptorTable	std.nogc_async_mut.gpu.object_vm.{...}	undefined: class folded into the object_vm oracle fns (descriptor_table.spl:29); object_vm_descriptor_spec is the superseded class-based spec, its 6 claims are only partly ported by descriptor_table_spec (resolve handles, miss coalescing, forged handle faults not ported)
1	GpuCasStore	std.nogc_async_mut.gpu.store.{...}	undefined: only CasStore exists, create/open API differs; spec stale
1	NVFS_STREAM_INGEST_PROVIDER_V1	std.fs_driver.nvfs_driver.{...}	whole streaming-ingest adapter (stream_ingest_begin/append/finish/abort_v1, evidence) missing; 3 specs name it
1	PropertyTrees	std.cc.entity.property_tree.{...}	cc module has no PropertyTrees/property_trees_new/ScrollNode; only an unrelated render_opt.PropertyTrees class exists
1	TextBlitCache	std.gpu.engine2d.helpers_text.{...}	whole cache (hits/misses/bucket/lookup_scan_count) missing
1	build_gcm_explicit_nonce_hex	std.http_server.worker.{...}	TLS 1.2 explicit-nonce AES-GCM records not implemented; worker_wire uses an implicit nonce, and the spec's 9 source-text contract strings are absent
1	generate_k26_soc_top_vexriscv	lib.hardware.fpga_k26.k26_soc_top.{...}	whole VexRiscv K26 top generator missing
```

## Fix direction
For each site, import from the defining module, or add an explicit `export` when the middle module really is the public facade. Flip the default once a full census, including the timed-out directories, is empty.

**Batch 3 follow-up (pre-existing failures, not a regression):** `test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl` gives 11 pass / 5 fail. The 5 failures are AC-3 TCL assertions: `add_files` for `.v`, the VexRiscv filename, `.v` extension, `S_AXI_HP0` enable, `PSU__USE__S_AXI_GP`/HP config. The base commit before batch 3 gives the identical verdict without strict. The `describe` titles name `SynthesisProject add_verilog_sources` / `enable_axi_hp_port`, which exist nowhere. Either implement those generator features or rewrite the spec against `generate_vivado_tcl_rv64`.

**Batch 4 follow-up:** unmasked pre-existing failures are filed in `strict_census_batch4_unmasked_failures_2026-11-27.md`.
