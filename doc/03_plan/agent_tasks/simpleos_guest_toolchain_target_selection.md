# SimpleOS Guest Toolchain Target Selection — Agent Plan

- Implementation owner: guest-toolchain target lane; immutable descriptor,
  focused CLI/pipeline plumbing, libc shims, and sysroot deduplication.
- Sidecar lanes: N/A for this bounded change; no mutable state crosses a task,
  actor, thread, process, or device boundary.
- Merge owner: root SimpleOS hardening agent.
- Final reviewer: independent normal/highest-capability guest-toolchain reviewer.
- Acceptance: all three admitted IDs map to exact triples and existing codegen
  targets; unknown IDs and linker target mismatches fail closed; the CLI selects
  once; x86-specific CPL policy is absent from Pure-Simple app code; canonical
  syscall assembly is consumed by each sysroot producer.
