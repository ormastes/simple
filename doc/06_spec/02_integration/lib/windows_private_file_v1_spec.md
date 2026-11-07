# Private Windows journal owner

Executable source: `test/02_integration/lib/windows_private_file_v1_spec.spl`.
Execution status: **NOT_RUN**, Windows fixture unavailable. This manual records
the intended executable scenarios, not evidence of successful native execution.

| Requirement | Fixture and real observation |
|---|---|
| REQ-WIN-PRIVATE-001 | An installed root granting foreign read access and a reparse root both fail admission; returned cleanup owners are closed explicitly. |
| REQ-WIN-PRIVATE-002 | A fresh private root admits a stage; exact written bytes survive seal, handle-relative no-replace publication and retained/fresh-handle readback. A conflicting stage cannot replace the final bytes. |
| REQ-WIN-PRIVATE-003 | A file copy made before seal cannot write after seal or publication. Copied stale file/root tokens cannot access or close a subsequently allocated owner. |

Provision a dedicated local fixed volume with installer-controlled ancestry.
Record independently observed owner SIDs, DACLs and reparse metadata. Provide
the three fixture paths documented in the design. Missing fixture paths fail
explicitly; unsupported host runs do not count as Windows evidence. Use a fresh
empty fixture directory for each execution because publication deliberately
does not replace existing receipt entries.

The source scenarios check file bytes, native security decisions, authoritative
phase transitions, exact close results and collision preservation. Production
qualification additionally requires an independent untrusted-user access oracle
and release-failure injection for retained cleanup handles and descriptors.
