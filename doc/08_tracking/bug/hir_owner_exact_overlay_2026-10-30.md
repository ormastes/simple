# Unconditional core-owner folding violates exact source-root precedence

Status: native baseline reproduced; repaired native validation pending.

Release c7446e9f134 rewrites every `compiler.core.X` declaration owner to
`compiler.frontend.core.X` without consulting an admitted source path. The
entry resolver tries exact `compiler/core/X.spl` before its numbered fallback
`compiler/10.frontend/core/X.spl`. Admitted-root lookup preserves that priority.
These two physically different sources may therefore own distinct declarations.

The seven-case `hir_owner_overlay_probe.spl` checks the production helper's
logical/physical normalization agreement and separation of those owners. The
native baseline returned exit 1 and printed a logical frontend owner alongside
the physical `compiler.core.overlay` owner. Selected SCV source hashes matched
the released helper and fixture. Artifact SHA256:
`afbae63376b47f0e98fdfac5200606e1c0bce8186858df37f228df2a009b62cb`.
Evidence: `/tmp/simple-hir-owner-overlay-red-c903-20261030`, peak 2,404,148 KiB.
Producer: admitted pure-Simple
`c903ca1b0361d436829f9252cd3b7bafa0aba472d4c98a0bcd7e2943d374505e`.
This baseline proves the helper collision; it does not execute the filesystem
resolver or the entire RTI pipeline.

The repair removes the unsupported global equivalence and preserves the
physical-owner monomorphization fix from fb18a7c374d. That fix derives ownership
from admitted module paths, including specialization placement, and retains
the existing provider validation. Owner-symbol and RTI tests now distinguish
unadmitted logical names from actual physical providers. The real generic
alias fixture under `test/01_unit/compiler/hir/admitted_alias_case` imports the
same physical provider through both supported spellings and checks ordinary
and specialized results. Its native result remains pending.

No frozen compiler target or prior evidence was changed. No wildcard rename,
RTI check suppression, or blanket claim of full runner qualification is made.
