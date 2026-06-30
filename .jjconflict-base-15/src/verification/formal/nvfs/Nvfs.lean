import Nvfs.Basic
import Nvfs.State
import Nvfs.Ops
import Nvfs.Invariants
import Nvfs.Theorems

/-!
# NVFS — Lean 4 State Model and Integrity Invariants

Top-level re-export for the NVFS formal verification project. Bring the
modules into scope with `import Nvfs`.

Modules:
* `Nvfs.Basic`        — primitive types (IDs, enums, checksums).
* `Nvfs.State`        — the filesystem world state (`FsState`).
* `Nvfs.Ops`          — transitions: `arena_create`, `arena_append`, ...
* `Nvfs.Invariants`   — I1 … I10 as predicates over `FsState`.
* `Nvfs.Theorems`     — preservation theorems per op + crash refinement.

See `/home/ormastes/dev/pub/simple/doc/01_research/nvfs_formal_verification.md`
for the methodology, scoping rationale and primary sources.
-/
