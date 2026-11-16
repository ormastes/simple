# Linux installed machine storage v1

These requirements record the parent orchestrator's explicitly selected,
bounded single-service-UID scope and the frozen reviewer contract. They do not
authorize installation, elevation, a new daemon/journal, runtime exports,
allowlist changes, builds or execution campaigns.

- **REQ-LINUX-MACHINE-STORAGE-001:** Open actual root-installed policy only from
  the fixed administrative root, with genuine current-task procfs/namespace,
  UID/GID, process incarnation and kernel boot provenance. Expose opaque
  readers and diagnostic data; caller paths and identity strings grant nothing.
- **REQ-LINUX-MACHINE-STORAGE-002:** Transfer into one fixed, predelegated,
  private service-UID state root; retain its actual writer for the entire
  storage lifetime, bind exact policy bytes, observe hardware capacity and
  reuse the existing immutable WAL. The authority additionally matches the
  selected provider's existing UID/identity/physical-scope pins and shares the
  physical budget. Missing history does not authorize a replacement charge.
- **REQ-LINUX-MACHINE-STORAGE-003:** Preserve cleanup owners across failures,
  reject aliases after transfer/close, refuse a competing writer, and consume
  Linux numeric descriptors once even when native close reports an error.
  Lazy fixed supervisor/workspace profile reads share this protected reader;
  their data alone cannot grant a supervisor, workspace effect or migration
  fence. Actual process-origin proof must survive all capsules closing.

Authored traceability: `test/03_system/tools/linux_machine_storage_v1_spec.spl`;
design and evidence limits: `doc/05_design/linux_machine_storage_v1.md`.
Status: **AUTHORED_NOT_RUN**. Negative native fixtures and ABI/link/runtime
admission are pending; no production readiness PASS is recorded.
