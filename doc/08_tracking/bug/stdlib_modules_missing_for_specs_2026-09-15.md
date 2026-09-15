# Modules/imports referenced by specs do not exist in src

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected specs (left RED) — missing subject
- gpu/provider_spec.spl — std.gpu.provider (no provider.spl under any gpu root)
- concurrent/server_worker_policy_spec.spl — std.concurrent.server_worker_policy
- cache_ttl_unit_seconds_spec.spl — std.time and std.cache (time lives at
  nogc_sync_mut/src/time.spl; no cache module)
- io/rt_hal_buffer_dispatch_spec.spl — std.nogc_sync_mut.io.hal_buffer_dispatch
- io/hal_device_callback_capsule_spec.spl — parse/resolution failure, subject absent
- io/window_winit_compat_mapping_spec.spl — winit_compat_event_get_type not found
- io/durable_atomic_bytes_spec.spl — file_atomic_write_bytes_durable (only the
  text file_atomic_write exists in io/file_ops.spl)
- sffi/package_sha256_spec.spl — package_sha256 not found under sffi/
- spec/scenario_evidence_manifest_spec.spl + scenario_evidence_manifest_io_spec.spl
  — std.common.spec.scenario_text_evidence / scenario_motion_evidence and
  std.spec.scenario_evidence_manifest(+_io) do not exist
- ui_test/gui_driver_spec.spl — std.ui_test does not export gui_driver
- ui_test/sgtti_strict_resolve_spec.spl — method resolve_strict missing on
  SgttiTestDriver
- gpu/chromium_reference_oracle_converter_spec.spl — `use
  test.helpers.web_chromium_reference_oracle` unresolvable (helper exists at
  test/helpers/ but no supported import path reaches it)

## Unblock condition
Per spec: restore the module, or port the spec to the replacement API /
sanctioned import path with a reviewed mapping.
