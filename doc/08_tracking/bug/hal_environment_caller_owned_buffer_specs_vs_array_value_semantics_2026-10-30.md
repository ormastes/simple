# HAL environment specs assume caller-owned `[u8]` out-parameters; arrays are value types (2026-10-30)

Status: OPEN — design gap between the restored HAL environment_instruction /
hal_provider packages and the normative array semantics. The affected spec
scenarios are marked `skip_it` with a link to this record.

## Context

The HAL `environment_instruction` and `hal_provider` packages were lost in the
2026-09-29 transplant (`88aac2ffe28`) and restored from `43e1f7108fb` (plus
the newer pieces that only exist in `a8244005f9b`). The restored code is the
2026-08-22 design: executors, replay, wire decoders and device adapters write
results into a **caller-owned `[u8]` parameter** (`result_bytes`,
`replay_result_bytes`, device model buffers), and spec helpers such as
`put_i64(bytes: [u8], offset, value)` fill frames in place.

`doc/04_architecture/compiler/array_value_abi_contract.md` §3.1 is normative:
arrays are value types; a callee's writes to an array parameter are invisible
to the caller. Measured on the deployed seed (`bin/simple`, 2026-10-30):

| probe | interpreter (`simple test`) | `--mode native` | `simple run` JIT |
|---|---|---|---|
| `fn put(b: [u8], i)` writes `b[i]` | lost | lost | visible (non-conforming) |
| `fn put(mut b: [u8], i)` writes `b[i]` | lost | lost | visible |

`simple test` runs every spec on the interpreter, so each scenario that reads
back a buffer a callee filled sees the original zeros.

## Affected scenarios (marked `skip_it`)

- `test/01_unit/lib/common/structural/environment_device_adapter_spec.spl` (3)
- `test/01_unit/lib/common/structural/environment_instruction_executor_spec.spl` (2)
- `test/01_unit/lib/common/structural/environment_instruction_wire_v1_spec.spl` (5) — `frame()` builds the wire frame through `put_i64`
- `test/01_unit/lib/common/structural/rt_hal_device_capability_api_spec.spl` (4)
- `test/01_unit/lib/common/structural/rt_hal_environment_binding_spec.spl` (1)
- `test/02_integration/app/hal_environment_entropy_executor_spec.spl` (2)
- `test/02_integration/app/hal_environment_physical_executor_spec.spl` (4; the clock scenario also calls `.execute` on `HostedPreparedClockReadExecutorV1`, which has no `EnvPhysicalExecutorPortV1` impl in any historical source)
- `test/02_integration/app/hal_environment_process_timeout_spec.spl` (1)
- `test/02_integration/app/hal_environment_socket_executor_spec.spl` (1)
- `test/02_integration/app/hal_tagged_environment_binding_spec.spl` (2 of 2) —
  every scenario is affected, so the file is tagged `@tag:in-development`
  instead (a spec with zero executed scenarios is reported as an error)

## Unblock condition

Either the HAL APIs return the filled buffer (the `arr = modify(arr)` form the
contract prescribes) and the specs consume the returned value, or `mut` array
parameters write back on the interpreter and native lanes as §3.2 requires and
the out-parameters are declared `mut`. Then remove the `skip_it` markers.

## Separate gap: runtime surfaces that were never restored

These specs import modules whose `rt_*` externs have no backing in the C or
Rust runtime at HEAD, so they stay red (the first two are tagged `@tag:in-development`):

- `test/02_integration/app/hal_environment_file_executor_spec.spl` —
  `rt_hosted_confined_{root_open,file_open,file_read_at,file_write_at,file_close}`
  (last present at `43e1f7108fb` in `src/runtime/platform/hosted_confined_file_impl.h`
  and `src/compiler_rust/common/src/runtime_symbols.rs`; dropped by the
  `a8244005f9b` squash merge, not by a commit that removed them on purpose).
- `test/01_unit/lib/nogc_sync_mut/io/hal_device_callback_capsule_spec.spl` —
  `rt_hal_device_route_prepare_v1` was never implemented in any runtime.
- `test/01_unit/lib/nogc_sync_mut/io/rt_hal_buffer_dispatch_spec.spl` —
  `rt_hal_buffer_dispatch_{direct,compare,configured}_v3` (last present at
  `43e1f7108fb` in `src/runtime/runtime_hal_buffer_dispatch.c`).

`rt_hal_buffer_dispatch_spec.spl` was already red before this restore and is left untouched.
Restoring them means restoring the C runtime sources, the Rust symbol table
rows and deploying a rebuilt seed; the `.spl` wrappers were not restored so no
new unbacked extern declarations enter the tree.
