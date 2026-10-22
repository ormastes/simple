# Phase 3 HIR journal discovery failure

The canonical Windows attempt10 froze release_phase3 source at
`9af03a7d3291c8a9044f884b2ecf5bccfb60683a`. Its Rust support builds and
C runtime admission completed, but stage2 native-build exited 1 during
discovery of `driver_hir_archive_journal_v1.spl` at 145:83:
`Unexpected token: expected expression, found Else`.

The journal used a multiline `if` expression whose `else` followed the
`Err(...)` expression on the same line. Put `else` on its own line at the
matching indentation, with `Ok(...)` in its branch. This preserves the
condition, both Result values, and the transient ownership operations.

The preserved stage2 receipt records peak RSS 49,056 KiB, limit
5,859,375 KiB, exit 1, and a quiescent process group. No new Simple compiler
was produced or admitted, and no dependent Hello World or runner test ran.
Evidence remains in `C:/dev/simple-phase3-bootstrap-evidence/attempt10` and
the frozen attempt10 `build/bootstrap` tree.

The corrected source layout has been independently reviewed. A fresh
canonical bootstrap must validate discovery and compiler admission; source
review and the diagnostic-classifier shell tests do not supply that proof.
