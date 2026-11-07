# Inspect ownership-flow transfer and branch behavior

**Status:** authored manual; executable Simple scenarios NOT_RUN; SPipe generation and maintenance scan pending admitted runtime. This manual is not a generated PASS artifact.

**Executable specification:** `test/00_formal_verification/compiler/ownership_flow_transfer_refinement_spec.spl`.
**Requirement:** FV-OWN-02 model refinement subset; full obligation remains open.
**Formal evidence:** The unchanged `src/verification/ownership_flow` model has retained historical Lean 4.30.0 build/28-root kernel traces. Original temporary stdout logs are missing; this release-based candidate has not rerun any proof or Simple scenario. See `doc/03_plan/release/1.0.0/ownership_flow_formal_refinement_2026-11-06.md` for precise boundaries.

1. Move two separate fields. Both remain in maybe-moved state, and repeating the second move does not duplicate it.
2. Reinitialize one field after a whole-object and two-field move. Only that covered field revives; the ancestor and sibling hazards remain. Reinitializing the whole object clears all remaining hazards.
3. Compare two symbolic array indices and two different constant indices. Symbolic indices may alias and cannot definitely revive a move; distinct constant elements do not overlap.
4. Read a different base and then a moved field through the real solver. The unrelated read succeeds; exactly the moved-field read reports its actual point.
5. Join two reachable branches in either successor order. A move from one predecessor remains a hazard at the joined read.
6. Terminate the moving branch before the join. Its move does not contaminate the surviving branch's valid read.
7. Write through a moved ancestor and then replace the exact moved owner. The descendant write fails; exact replacement followed by revival permits a later read.
8. Set the solver work budget to zero. Analysis fails explicitly instead of treating an incomplete check as success.

These checks call actual production functions. They do not establish HIR extraction completeness, runtime cleanup or full CFG proof. Generated captures and an admitted runner receipt are required before this scenario's execution status changes.
