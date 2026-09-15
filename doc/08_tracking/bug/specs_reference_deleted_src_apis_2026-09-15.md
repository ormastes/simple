# Specs reference src APIs that no longer exist (2026-09-15)

Verified failing under plain `bin/simple run` (not wrapper artifacts). Each spec calls a
symbol that exhaustive `src/` grep cannot find under any module; the subject was deleted
or renamed without a spec update. One record for the family; unblock condition per item.

| Spec (test/01_unit/lib/nogc_async_mut/) | Missing symbol | File:line of call |
|---|---|---|
| http_server/tls_record_capability_spec.spl | `tls_record_path_admits_min_version` | spec semantic error |
| quic/quic_udp_initial_spec.spl | `build_unprotected_initial_shape` | spec semantic error |
| io/driver_write_completion_spec.spl | `io_sendfile_chunk_truncated_v1` (and `io_write_completion_has_progress_v1` family) | spec semantic error |
| debug/coordinator_service_adapter_v1_spec.spl | `DebugCoordinatorServiceAdapterV1` (`std.nogc_async_mut.debug.coordinator_service_adapter_v1`) | spec line 6 |
| debug/legacy_service_adapter_v1_spec.spl | `legacy_service_adapter_v1` export | spec import |
| concurrent/multicore_green_try_spawn_contract_spec.spl | `multicore_green_try_spawn` | spec semantic error |
| http_server/async_handler_registry_spec.spl | `submit_async` on `HandlerRegistry` | spec semantic error |
| http_server/connection_drain_spec.spl | `set_response_bytes_draining` on `Connection` | spec semantic error |
| http_server/async_handler_lifecycle_spec.spl | export `async_handler_lifecycle` of `std.http_server` | spec import |
| http_server/h2_async_dispatch_spec.spl | export `h2_async_dispatch` of `std.http_server` | spec import |
| tui/widgets/tui_widgets_facade_spec.spl | `default_style` | spec semantic error |
| game2d/asset/game2d_asset_facade_spec.spl | `Span` | spec semantic error |
| engine/scene/engine_scene_facade_spec.spl | field `index` on `RawHandle` | spec semantic error |
| concurrent_ds_spec.spl | method `has` on `ConcurrentMap` | spec semantic error |
| sosix/posix_spec.spl | extern `rt_fd_pread` / `rt_fd_pwrite` (unknown extern) | spec extern decl |
| web_ui/web_ui_facade_spec.spl | `EngineDomBackend` missing trait method `body_id` from `DomBackend` | src trait break |

Unblock condition: re-add the API under its old name (preferred for externs
`rt_fd_pread`/`rt_fd_pwrite`), or land a reviewed rename mapping and update the specs in
the same change. Specs stay RED until then; assertions were not weakened.
