# Seed: file_write_bytes silent no-op and `# @timeout_secs` ignored (symbol-table gap for the rt_array_bytes_* family)

Status: fixed 2026-10-24 on release/1.0.0 (work/seed-io-write-timeout-20261024);
see the merge commit for the exact change set.

## Symptoms

1. `std.io_runtime.file_write_bytes` (and the whole
   `std.nogc_sync_mut.sffi.file_bytes` native write path) returned success or
   `false` without creating/updating the file when a spec ran under the Rust
   seed (x86_64-pc-windows-msvc, bootstrap profile). Observed 2026-10-23 on the
   integration lane (PR #4193 review); specs routed around it with committed
   generator fixtures and a hex-via-text-write oracle
   (test/01_unit/lib/database/sqlite_format/writer_spec.spl).
2. The same seed lane ignored `# @timeout_secs <N>` spec headers: long specs
   (KDF iteration measurements) were capped at the runner client's default
   budget instead of the declared bound.

## Root cause (both defects, one family)

PR #4182 (8ba019e7781) added the compiler-owned RUNTIME_FUNCS contracts and
the interpreter twins for `rt_array_bytes_validate` /
`rt_array_bytes_copy_checked`, but not the third leg: the entries in
`common/src/runtime_symbols.rs::RUNTIME_SYMBOL_NAMES` that the JIT's static
symbol provider uses to resolve a name to an address. The same table also
lacked `rt_array_bytes_basis_len` / `rt_array_bytes_basis_ptr` (no contracts
either), and the whole `rt_io_file_*` read family except `rt_io_file_open`.

Consequences under the seed's default JIT lane
(`driver/src/exec_core.rs::run_file_jit`):

- A call whose symbol the provider cannot resolve is demoted to a
  hybrid-interp-splice (`[engine-demotion] reason=hybrid-interp-splice`), which
  re-enters the interpreter through `rt_interp_call`.
- The splice bridge (`codegen/instr/core.rs::compile_interp_call` →
  `runtime_bridge.rs::runtime_to_value`) decodes a *packed* `[u8]` heap array
  into a boxed element `Value::Array`. The `rt_array_bytes_*` twins reject
  boxed/UInt-element arrays, so `rt_array_bytes_basis_len` returned -1 and
  `rt_array_bytes_validate` returned -22; `file_write_bytes_runtime_native`
  then returned `false` before ever reaching `rt_file_write_bytes_array`.
  Measured with `SIMPLE_DEBUG_FWB=1` on a two-call probe: the direct extern
  call reached `rt_file_write_bytes_array` and wrote; the cross-module
  stdlib call died at the twin with `arg_variant=Array`.
- `std.io_runtime.file_write_bytes` resolved (same-signature co-compiled
  winner in the flattened module) to the `nogc_sync_mut.io` variant, which
  routes through `file_write_bytes_tagged_native` — i.e. exactly through the
  spliced family above. The pure-Simple lane binds the same import to
  `nogc_sync_mut.io_runtime.file_write_bytes`, whose direct
  `rt_file_write_bytes` extern call works, which is why the defect was
  seed-only.
- The test-runner client's directive parser
  (`src/app/test_runner_new/test_runner_client.spl::_spec_timeout_secs_directive_text`)
  reads the spec via `std.io_runtime.read_file_text` → `file_read_result` →
  `FileTextSession` → the spliced `rt_io_file_read_all`. With the session read
  failing, the parse saw empty content, `declared = 0`, and the client kept
  its default budget — the fixed ~900 s observed on the lane.

The seed's own native test runner
(`driver/src/cli/test_runner/execution.rs::per_test_timeout_secs`) also had no
directive parsing at all, so `SIMPLE_TEST_RUNNER_RUST=1` lanes could not honor
a raised bound either.

## Fix

- `common/src/runtime_symbols.rs`: register `rt_array_bytes_validate`,
  `rt_array_bytes_copy_checked`, `rt_array_bytes_basis_len`,
  `rt_array_bytes_basis_ptr` in RUNTIME_SYMBOL_NAMES so the JIT resolves them
  directly against the Rust runtime exports (value/collections.rs).
- `compiler/src/codegen/runtime_sffi.rs`: add the two missing compiler-owned
  contracts `rt_array_bytes_basis_len [i64]->[i64]` and
  `rt_array_bytes_basis_ptr [i64]->[i64]` (the other two landed in #4182).
- `compiler/src/codegen/runtime_sffi.rs` + `runtime_symbols.rs`: register the
  `rt_io_file_*` descriptor family the FileTextSession read path needs and the
  Rust runtime exports (`rt_io_file_read_all`, `rt_io_file_read`,
  `rt_io_file_close`, `rt_io_file_seek`, `rt_io_file_flush`,
  `rt_io_file_meta_size`) with their contracts, so session reads are direct
  calls instead of splices.
- `driver/src/cli/test_runner/execution.rs`: `per_test_timeout_secs` now
  parses `# @timeout_secs <N>` exactly like the pure-Simple single runner
  (`spec_timeout_secs_directive` in
  src/app/test_runner_new/test_runner_single.spl — first occurrence of the
  16-byte key, run of ASCII digits, 0 when absent/digitless) and raises —
  never lowers — the computed budget. `SIMPLE_TEST_TIMEOUT` stays the most
  specific override.

## Evidence

- Before (tip 63dfb17ba91 seed): probe_io_run `write_ok=false`, file absent;
  probe_read stdlib `file_read` len 0 while the direct extern returned the
  content and `file_read_bytes` worked; directive probe `content_len=0`.
- After: test/01_unit/app/bug/seed_file_write_bytes_spec.spl 3/3 VERDICT OK;
  the directive probe prints `declared=1500`;
  test/01_unit/lib/database/sqlite_format/* and
  test/01_unit/app/bug/bug_snapshot_crc_spec.spl stay green.
