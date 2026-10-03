# SimpleOS CLI ignores canonical aliases and explicit guest defaults

Status: OPEN; owner: item1_astra_impl; final reviewer: root.
Baseline: `50d73b7abfb1c8a607ca0c692f825d07fe2ec8e0`.
Requirements: simple_platform_unification REQ-001, REQ-011, REQ-016, REQ-022.

Source finding: `src/os/_QemuRunner/os_build_run.spl:93` maintains a separate
architecture-name list that rejects `simpleos-x86_64` and canonical userland
triples. `src/os/cli.spl:59` converts every default other than literal `arm64`
to `x86_64`, discarding explicit RV64/RV32/ARM32 and canonical overrides.
`src/os/_QemuRunner/runner_targets.spl:165` also turns unknown host discovery
into an inferred AMD64 guest. These are production selection gaps, distinct
from missing native evidence.

Claimed fix: use the existing registry's SimpleOS CLI identity projection;
keep board/host/kernel-build identities outside the architecture-only CLI
projection. Preserve explicit defaults and reject unknown values. Explicit
CLI arguments continue to override environment selection.

TDD: exact and adjacent behavioral scenarios are authored before source edits.
RED/GREEN, SSpec/docgen and native CLI evidence are UNRUN: no qualified runtime
is available, and no seed or heavy build is substituted. Keep this record open
until the focused tests and real CLI target matrix run on an admitted runtime.
