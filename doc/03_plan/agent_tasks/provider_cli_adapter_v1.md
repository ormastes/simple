# Provider adapter ownership and review

- App adapter/data/collector owner: `provider_scope_inventory_sol_20261115` in
  `/tmp/simple-caret-provider-adapters-20261115`, branch
  `work/caret-provider-adapters-20261115-sol`.
- Common/backend actual configuration and bounded output observation:
  `podman_command_fix_20261114`, separate source scope. App owner does not edit
  those leaf/query files.
- Interface/final architecture reviewer: `astra_caret_groundwork_review_20261115`.
- Merge owner: root. Exact source snapshots require Astra review before landing.
- Additional sidecars: N/A; no subagents spawned by this worker.

Keep Caret `main.spl`, source leases, runtime-provider files, accepted inventory
and prior cutoff lanes outside this patch. Do not duplicate an executor, PTY,
admission service or runtime export. The existing Host/common execution owners
remain authoritative; deadline/admission DTOs cannot mint new execution rights.

Data slice is authored. Next app source depends on the frozen actual common
configuration/output API. Actual probe and task consumers must own their native
progress; local CLI probes remain research rather than container attestation.
No host task fallback is authorized. Maximum aggregate CPU is five; research
probes ran sequentially with one CPU affinity. Verification/fix cycle 1 is
source inspection only; no runtime/native/bootstrap campaign was executed.
