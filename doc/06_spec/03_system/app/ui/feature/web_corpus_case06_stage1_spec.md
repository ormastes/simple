# Web corpus case 06 Stage 1 admission

Manual companion to
`test/03_system/app/ui/feature/web_corpus_case06_stage1_spec.spl`.
Generated SPipe output is pending a trustworthy Simple runner.

## Scenarios

1. A one-pixel change to the pinned child offset changes the source digest and
   is rejected before Web layout admission.
2. The pinned source produces six Web commands. The transparent overflow
   parent remains in source DrawIR; five visible commands reach GPU DrawIR
   with source indexes `0,1,2,3,5`.
3. The GPU child keeps the producer's 220 × 170 box at `(80,65)` and its
   parent-derived clip `(40,40,160,100)`. Source DrawIR digest, component
   identities, paint order and command mapping remain linked.

Requirement links: REQ-2D-006, NFR-2D-002. These are executable assertions,
but no trustworthy execution result is available yet.
