# P-static Backend Edits Do Not Rebuild The Kernel

- Executable: `test/02_integration/bootstrap/plugin_edit_no_rebuild_spec.spl`
- Requirements: `KPM-NFR-004`, `KPM-NFR-006`, `KPM-REQ-001`, `KPM-REQ-007`, `KPM-REQ-008`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- keeps bootstrap kernel inputs stable under a backend implementation mutation.
- rejects every K0 or K1 dependency on a P-static backend.
- keeps optional backend composition outside the compiler kernel.
- rejects every direct or policy-unbound backend dispatch bypass.
- keeps native object scope stable when only P-static source bytes change.
- is mutation-red when the kernel identity changes.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
