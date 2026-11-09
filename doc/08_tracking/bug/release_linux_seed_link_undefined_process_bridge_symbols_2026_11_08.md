# Linux bootstrap Rust seed fails to link: process-bridge symbols without an owner

Canonical ID: `release_linux_seed_link_undefined_process_bridge_symbols_2026_11_08`

Status: fix-implemented-verification-pending. Found while trying to verify
`release_stage1_native_build_worker_sigsegv_2026_10_20` natively; this bug is
upstream of it (no stage1 can be built until the seed links).

## Failure

release.yml run 42457312983 (workflow_dispatch on `release/1.0.0` @ 0ee4e247c0d,
GitHub-hosted `ubuntu-latest`), job 128659173410, step "Build native Linux
x86_64/arm64 binary via bootstrap-only Rust seed":

```
cargo build --profile bootstrap -p simple-driver
error: linking with `cc` failed: exit status: 1
rust-lld: error: undefined symbol: simple_process_stdout_take_v1
  >>> referenced by runtime_socket_nonblock.c (rt_local_unix_stage_stdout_v1)
rust-lld: error: undefined symbol: simple_process_byte_adopt_v1
  >>> referenced by runtime_socket_nonblock.c (rt_local_unix_adopt_byte_endpoint_v1)
rust-lld: error: undefined symbol: rt_process_stream_launch_not_started_v2
rust-lld: error: undefined symbol: rt_process_stream_publish_broker_v2
rust-lld: error: undefined symbol: rt_process_stream_claim_launch_v2
  >>> referenced by runtime_process_owned.c (rt_lg_launch_broker_mode_v2)
error: could not compile `simple-driver` (bin "simple-stub")
```

The same five symbols fail again for `-p simple-native-all --features driver-compat`.

## Root cause

The 2026-11-07 process/daemon commits on `release/1.0.0` (`0827b39023c`
"owned local gateway framing and byte endpoint transfer", `99a3ff374c6`
"owned Unix byte connections", and the `5f5fa3a95f3` process lineage) made two
seed-compiled translation units call into the piped-process registry:

- `runtime_socket_nonblock.c` includes `runtime_local_unix_v1.h` ->
  `runtime_local_unix_transfer_v1.h`, whose Linux branch calls
  `simple_process_stdout_take_v1` / `simple_process_byte_adopt_v1`.
- `runtime_process_owned.c` includes `runtime_linux_group_owner_impl.h` on
  Linux, whose `rt_lg_launch_broker_mode_v2` calls `rt_process_stream_*_v2`.

All five are defined only in `runtime_process.c` (the v1 pair via
`runtime_piped_byte_endpoint_v1_impl.h`, included at `runtime_process.c:4634`),
over its private `s_procs` / `s_proc_lock` registry. `runtime_process.c` is not
in the seed's `c_sources` (`src/compiler_rust/runtime/build.rs`) because it
collides with Rust-owned `rt_process_*` APIs, so the Linux seed has callers
without an owner. Windows is unaffected (both call sites are `__linux__`-only);
macOS is unaffected for the same reason. `main` does not carry these commits
(the files are 2,600 lines shorter there), so the regression is release-only.

## Fix

`src/runtime/runtime_bootstrap_process_bridge_unavailable.c`: a seed-only
Linux TU that defines the five bridges and answers exactly what the canonical
owner answers when no stream/endpoint slot exists — `-4` (unsupported lane) for
the v1 byte-endpoint bridges, `ESTALE` for the v2 stream bridges, `EINVAL` on
null out-pointers / non-positive broker pid — with every out-parameter cleared.
Nothing is reported as success. Registered in `build.rs` (`linux_uring` block,
plus `rerun-if-changed`) and in
`scripts/check/runtime_source_list_parity_baseline.txt` as `rust` only; the
full C runtime keeps linking `runtime_process.c` and never this file.

Prevention test: `src/runtime/test/bootstrap_process_bridge_unavailable_selfcheck.c`
links the provider with the consuming headers' prototypes (never
`runtime_process.c`) and asserts every bridge resolves and fails closed.
Existing gate that would have caught this with a Linux host:
`scripts/check/check-seed-builds-push.shs` (cargo check does not link; the
ratchet that does is the release.yml seed build itself).

## Verification needed

A release.yml run on `release/1.0.0` whose linux-x86_64 job passes the seed
build step and reaches stage1 (`Native-built Simple binary verified`). Then the
original bug's "Create distribution package" step becomes observable again.
