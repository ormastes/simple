# SOSIX runtime unification research — index and repo verification

Three external research deliverables (2026-09-05), saved verbatim, plus the
repo check that decides which of their claims still hold at
`56d032e6f0d` (HEAD, 2026-09-05; host `aarch64-unknown-linux-gnu`;
`bin/simple` = Rust seed). Design and plan derived from them:
`doc/05_design/runtime/sosix_runtime_unification_design.md`,
`doc/03_plan/agent_tasks/sosix_runtime_unification_parallel_plan_2026-09-05.md`,
lane `.spipe/sosix_runtime_unification/state.md`.

| File | Content |
|---|---|
| `simple_sosix_runtime_unification_combined_v1_2026-09-05.md` | Design + WP-01..12 plan + FR-SOSIX-DQ-001..012 + source register (snapshot `320e6d9`) |
| `simple_sosix_runtime_unification_design_plan_2026-09-05.md` | Second pass: D01..D12 decisions, RU-001..090 plan, V01..V32 tests (snapshot `27f1973`) |
| `simple_os_gpu_queue_feature_requests_2026-09-05.md` | GQ-001..012 SimpleOS device-queue backlog |

Both cited snapshots are local ancestors (`git cat-file -t` = commit).

```sdn
verification:
  verified:   [host_facade R1, io_rw busy-wait+serial-write-fabrication R2,
               operation.spl wrap-to-1 R3, ids 0x0101/0x0102 R4,
               future_compat_adapter, raw_rt_access WARNING, runtime_symbols tiers,
               driver_provider_contract_v1, bug no_renaming_re_export E1002]
  missed:     [src/os/sosix/host (ids 0x1001 0x1002 0x1101 0x1201 + config snapshot),
               src/os/sosix/fs positioned v1 stack (syscalls 134/135, registered buffers),
               src/os/sosix/core completion_queue(1024) wait_set(256) sync_wait_adapter,
               src/os/sosix/io.spl is a divergent copy of io_rw.spl (no importer found),
               3 real Future impls + 2 one-line shims, 72 sosix specs exist]
  stale:      [direct-rt baseline is 7776 not 12948,
               "no retirement/wait owner" — sync_wait_adapter never spins; io_rw just bypasses it]
  blocking:   [no fd-level pread/pwrite rt_* primitive in hosted runtime,
               no bare-libc extern mechanism in src/lib -> exact alias = runtime-owned change]
```
