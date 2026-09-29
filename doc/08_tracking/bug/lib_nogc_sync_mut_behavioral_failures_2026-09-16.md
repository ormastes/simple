# lib nogc_sync_mut: behavioral/spec failures beyond trivial repair (22 specs RED)

**Status:** OPEN (2026-09-16). All verified with `SIMPLE_TIMEOUT_SECONDS=600 bin/simple test <spec>`
on `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed banner present).

## Observed (spec -> failing example -> message)

- `fs_driver/positioned_binary_backend_parity_spec.spl` (0/11): `semantic: method
  'pread_bytes_handle' not found on type 'DbFsDriver'` (also `pread_bounded_bytes_handle`,
  `file_generation_v1`). The methods exist on `NvfsDriver`
  (`src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl:204,212,131`) but NOT on `DbFsDriver`
  (`src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` has only the private
  `_pread_inode_bytes_from_device_locked`). Also one expectation mismatch
  `FsError::TooLarge` vs `InvalidArg` on negative-offset pwrite.
- `engine/render/gpu_mesh3d_spec.spl` (2) and `engine/render/graph_ir3d_spec.spl` (1):
  runtime `semantic: method 'transform_direction' not found on type 'Vec3'` during
  software-backend draw. The method is defined on Mat4
  (`src/lib/common/engine/math3d.spl:272`); the 3D draw path dispatches it with the
  wrong receiver type.
- `engine/render/shader_compile_spec.spl` (5/17): WgslEmitter emits `void main() { ... }`
  with no `@vertex`/`@fragment` entry-point markers (output itself says "best-effort
  token-level transpilation"); one other example fails with
  `method 'len' not found on type 'i64' (receiver value: 0)`.
- `gpu/gpu_queue_usm_spec.spl` (4/34): `semantic: panic: E_GPU_COMPILE_ONLY:
  gpu_block_id_x is only valid after GPU compiler lowering` — spec exercises these
  intrinsics on a path that does not go through GPU lowering.
- `web_framework/session_csrf_signing_spec.spl` (3/11): `assert_equal failed: expected
  76e6d0e8..., got 00000019000000b5...` — sha256-style hex digests come back as raw
  little-endian word dumps, plus one `assert_true failed: got false`.
- `concurrent_thread_lifecycle_spec.spl` (1/2): repeated `handle.join()` after a
  completed join returns `Option::Some(0)`; spec (and docstring contract) expect nil.
- `concurrent_thread_pointer_spawn_spec.spl` (1/1): "passes closure pointers instead of
  forwarding closure Any values" — `expected false to equal true`.
- `concurrent/with_lock_guard_spec.spl`: runner reports `child-died-by-signal` /
  `TERMINATED: child produced no exit status` — crash in the lock-guard path.
- `env_platform_process_owner_spec.spl` (1/1): ownership-contract scan fails;
  `src/lib/nogc_sync_mut/env/platform.spl` no longer routes through
  `io.env_ops.{home_raw, cwd_raw}` / `process_ops` / `sysinfo_ops` (it now uses
  `std.env.types.{...}` directly), and `env/types.spl:27` export list gained
  `rt_env_get_i64, rt_platform_name`.
- `file_read_single_return_type_spec.spl` (2/9): source-scan guard finds 2
  optional-returning `file_read` definitions (expects 0) and 16 vs 18 plain-text
  return definitions — the io read API drifted from the single-return-type contract.
- `io/stream_reader_append_shape_spec.spl` (2/4): guard finds
  `src/lib/nogc_sync_mut/io/tcp.spl:828: buf = buf + chunk!` — the quadratic
  accumulator the spec forbids is still present in tcp.spl.
- `io/window_winit_compat_mapping_spec.spl` (2/2): `function
  'winit_compat_event_get_type' not found` / `'winit_compat_event_window_close_requested' not found`.
- `gpu/engine2d/simd_isa_provider_dispatch_spec.spl` (2/11): `function
  'simd_isa_copy_span' not found`, `'_kernel_probe_copy_bucket' not found`.
- `linalg/raw_memory_owner_spec.spl` (0/4): `function 'raw_f64_to_bits' not found`;
  plus inline-owner source-shape and staging-topology expectations drifted
  (`expected 0 to equal 4`).
- `js/engine/interpreter_object_single_owner_spec.spl` (1/1): `expected 3 to equal 2`
  (object allocation count).
- `js/engine/js_vm_reclamation_spec.spl` (0/4): retain/trace/release/counter examples
  all fail.
- `mission_critical/domain_arena_v1_spec.spl` (3/14): staged/committed byte isolation,
  forged-subspan rejection, malformed relaxed-profile rejection.
- `io/durable_atomic_bytes_spec.spl` (1/1): "publishes arbitrary bytes and cleans
  staging files after rename failure".
- `tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl` (0/2): lint crash
  regression specs ("does not crash lint ...").
- `test_runner/native_binary_resolution_contract_spec.spl` (1/1): "honors SIMPLE_BINARY
  before argv and deployed fallbacks" — the resolution order contract fails against
  `test_runner_parse.spl`'s current behavior.
- `ui/ui_scene_column_arena_v2_spec.spl` (3/8): lease partitioning, dirty-storage
  bridging, and the "two warm generations, zero commit-copy bytes" gate all
  `assert_true failed: got false`.

## Environment-limited (not code defects on this host)

- `concurrent/channel_scalar_abi_spec.spl`, `channel_owned_capsule_contract_spec.spl`:
  native C leg fails with `fatal error: 'unistd.h' file not found` — the host clang
  used by the spec cannot find core hosted headers.
- `engine/render/vulkan_backend3d_spec.spl` (2/36): `failed to open device
  /dev/dri/renderD128 (VK_ERROR_INCOMPATIBLE_DRIVER)` — no usable GPU on this host.

## Impact

22 specs ERROR on real behavioral gaps; 3 specs blocked by host environment. These are
correct specs failing against incomplete/incorrect implementations (testing rules: leave
RED, do not weaken).

## Expectation

Each numbered item above is fixed in `src/lib` (or `src/app` for the lint/test_runner
items) until its spec reaches outcome=OK.

## Unblock condition

Per-item owner implements the missing behavior/renames receiver correctly; re-run each
spec with `SIMPLE_TIMEOUT_SECONDS=600 bin/simple test <spec>`. The two env-limited
families need a host with hosted C headers and a Vulkan-capable device (or a recorded
skip decision).
