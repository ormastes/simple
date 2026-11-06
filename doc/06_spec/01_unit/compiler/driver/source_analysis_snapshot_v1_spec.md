# Immutable provider admission

Source: `test/01_unit/compiler/driver/source_analysis_snapshot_v1_spec.spl`.

Admit overlay bytes with recomputed SHA256; read the entry twice and require one dependency receipt. Reject forged/duplicate/traversing inputs and exhausted limits. Install one serial owner, verify file/directory membership, reject overlap, remove it and require reads to refuse. Resolve a virtual numbered import with the actual canonical resolver and a bounded work counter. Compare request identities across changed source, lifetime and environment.

Status: **NOT_RUN**. This is an authored obligation manual, not generated execution evidence. Requires an admitted self-hosted compiler and full original diagnostic producer capture. Runtime regeneration, semantic behavior, cancellation, startup/latency/RSS and release admission remain pending.
