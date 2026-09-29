# Linker handoffs — 2026-09-18

Filed by mold-MDSOC++ linker plan lane A0
(`doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md`, design
`doc/05_design/compiler/linker/mold_mdsocpp_linker_design.md`). These are
handoff records only — A0 does not implement either item and does not edit
the files named below.

## (a) S1 schema owner — generate `Link*V1` bindings

Owner: KPF fabric S1 schema/ABI lane (`src/tool/kernel_plugin_schema/**`).
See ledger row "LINK (facets only)" added in
`doc/03_plan/agent_tasks/kernel_plugin_fabric.md`.

Request: generate C/Rust (and eventually Simple) bindings for
`LinkRequestV1`, `LinkExecutionPolicyV1`, and `LinkReceiptV1` from the S1
schema generator once the linker plan's lane A2 struct shapes
(`src/lib/common/linker/{link_request_v1,link_policy_v1,link_receipt_v1}.spl`)
are frozen.

Until this handoff is picked up: `Link*V1` stay plain Simple structs in
`src/lib/common/linker/` with `KpfSchemaHeaderV1` headers and hand-written
total decoders (design D8) — no generated bindings exist yet.

## (b) SOSIX plan owners — request lanes H10–H12

Owner: `doc/03_plan/runtime/sosix_host_interface_only_plan_2026-09-18.md`
(today has lanes H1–H9; this file is not edited by the linker lanes). The
table below is copied verbatim from design §8 for the SOSIX plan owners to
triage as new lanes.

| Need | Proposed leaf (new file) | Blocks |
|---|---|---|
| mmap file windows | `sosix/host_map.spl`: `sosix_map_window(fd, off, len, prot) -> SosixWindow`, `sosix_unmap_window` over `smf_mmap_native._sffi_mmap_raw` | fast input residency, bounded windows |
| worker pool | `sosix/host_workers.spl`: `sosix_parallel_for(n, chunk, body)` over `nogc_sync_mut/concurrent/thread.spl` | fast variant `max_workers > 1` |
| memory limit + peak | `sosix/host_mem.spl`: `sosix_job_scope_create(limit_bytes)`, `sosix_job_scope_peak` (cgroup v2 / setrlimit fallback = `MeasuredOnly`) | G3 acceptance |

Until these land: linker plan lane A8 (bounded + compositions) stays
single-threaded for the fast path and `MeasuredOnly` for accounting, which
cannot close linker plan gate G3. `host_facade.spl` is H4-exclusive, so each
proposed leaf above is a new file, not an edit to it.
