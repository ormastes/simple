# Shared readonly private IO capability

Source: `test/02_integration/lib/windows_private_read_v2_spec.spl`.
Status: **NOT_RUN**. No Windows/native build or execution was authorized.

| Requirement | Actual observation authored |
|---|---|
| REQ-WIN-READ-001 | Two readonly handles open and read the same installed file while both remain retained. The native fixture retains nine plus nine readers. |
| REQ-WIN-READ-002 | Forging a V1 view cannot write, seal, publish or close the readonly kind; kernel WriteFile through the underlying readonly handle is denied. |
| REQ-WIN-READ-003 | A missing readonly child is refused without creation. |
| REQ-WIN-READ-004 | Successful shared handoff closes RW, checks exact file ID/size/bytes/security and returns only a readonly owner. |
| REQ-WIN-READ-005 | Failed RW close retains the exact cleanup owner and historical publication fact; a real final-name replacement returns a rejected readonly cleanup owner. |
| REQ-WIN-READ-006 | Actual V1/V2 roots compare using volume GUID plus native file ID; mismatch and invalid kind refuse, and failed descriptor release remains attributed to its owning root. |

Provision `SIMPLE_WINDOWS_PRIVATE_READ_INSTALLED_ROOT` for the Simple spec with
the documented `artifact.sdn`. Provision a separate fresh empty private root in
`SIMPLE_WINDOWS_PRIVATE_READ_EMPTY_ROOT` for the authored native fixture
`src/runtime/test/rt_windows_private_read_v2_selfcheck.c`. Root privacy and
installer-controlled ancestry must be independently established. These are
generic IO scenarios, not deployment, enrollment or executable-role admission.
Assertions cannot erase Simple scenario cleanup: every owner is retained in a
module-level canonical slot before checks, and only successful close clears it.
The native fixture refuses NDEBUG compilation; all actual checks remain active.
