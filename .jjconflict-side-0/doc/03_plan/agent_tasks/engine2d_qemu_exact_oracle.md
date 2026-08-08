<!-- codex-plan -->
# Engine2D QEMU Exact-Oracle Agent Tasks

## Ownership

- TODO owner: TODO529.
- Merge owner: the session integrating `engine2d_in_qemu_spec.spl` after all
  active worktree changes are reconciled.
- Final reviewer: normal/highest-capability model or human, independent of the
  oracle producer.

An active worktree currently owns the executable spec. Other agents must not
edit or overwrite it until that lane is reconciled. In particular, reject any
staged version that restores direct `rt_env_get`, `rt_process_run*`, Python QMP,
tolerance, skip-on-missing-QEMU, or automatic baseline creation.

## Sidecar Lanes

| Lane | Scope | Deliverable |
|---|---|---|
| x86_64 | Migrate the minimal fixture to the canonical production target and strict QMP path | Fresh ELF/serial/capture row |
| AArch64 | RAMFB/display entry through canonical Draw IR/Engine2D | Fresh row using the shared SSpec interface |
| RV64 | VirtIO/display entry through canonical Draw IR/Engine2D | Fresh row using the shared SSpec interface |
| Evidence schema | Extend the canonical owner or obtain approved requirements clarification for the four documented REQ-018 gaps | Validated schema used by every ISA row |
| Oracle | Independent per-ISA scene oracles and provenance | Three PPMs, SHA-256 values, provenance notes; no guest-source reuse |
| Review | Diff, generated manual, exclusions, evidence | PASS/FAIL report and TODO recommendation |

Before implementation, every lane uses `_engine2d_targets`, `_nonblack`,
`_oracle`, the row-specific post-present markers, and the exact `step("...")`
names defined in the system-test plan. Incomplete lanes use `fail(...)`, never
a dummy assertion or silent skip. The evidence-owner lane must also resolve the
REQ-018 schema gaps identified in the system-test plan without inventing guest
evidence.

## Merge Gate

Merge only after overlap is resolved, all three target entries are real, the
oracle is independently admitted, the pure-Simple compiler is valid, each live
row passes once, direct runtime/process guards pass, and the generated manual
matches the executable spec. Until then TODO529 remains open.
