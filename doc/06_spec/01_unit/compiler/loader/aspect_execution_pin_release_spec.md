# Bound execution pins survive ordinary release refusal

Requirement: P4 dynamic/profile lifetime closure; AD-01; existing REQ-L06-A06
and REQ-L06-A07. Executable scenario lives in
`test/01_unit/compiler/loader/aspect_final_unpin_v3_authority_spec.spl` under
“retains both pins when another bound reference still executes”.

1. Admit the existing real startup SMF fixture, acquire A and B, then begin two
   execution leases through A. Observe two aspect pins and one retained mapping.
2. Attempt ordinary release of A. It must return false, preserve active A and
   both pins, and leave mapping/unload observations unchanged.
3. Attempt final association through B. It must report
   `dynsmf-owned-library-query-drain-pending`. Repeat A release while Closing;
   both pins still remain.
4. Complete one A lease; replay of that completion must return false. A release
   must still refuse because the second execution remains live.
5. Complete the remaining lease. A release now succeeds once. A duplicate
   release and new execution fail, one B pin remains, and no unmap has occurred.
6. Associate and release B. Observe acknowledged physical release, one unload,
   no remaining mapping, and a replay with no second native dispatch.

Evidence: authored before the production guard, source-predicted RED only.
Status: UNRUN. No compiler, test runner, native call, build or benchmark was
launched. Existing single-reference drain and no-execution controls are retained
unchanged, not reported as executed. Runtime/backend/concurrency qualification is
required before a production PASS; this manual is not generated runtime output.
