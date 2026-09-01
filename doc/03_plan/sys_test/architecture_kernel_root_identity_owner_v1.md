# Architecture kernel-root identity acceptance plan

- Capture each x86/ARM/RISC-V kernel root only from live architecture readback.
- Reject zero roots, disabled SATP translation, invalid widths, and overflowing encodings.
- Reuse one identity for an exact architecture/width/root tuple.
- Keep identical physical roots from different architectures as distinct identities.
- Complete an exact same-identity switch without register write or outgoing release.
- Reject switch entry without an owner-held interrupt-quiescence precondition.
- Reject x86/ARM readback when non-root register attributes differ.
- Reject equal physical roots carrying different mapping identity or generation.
- Confirm distinct-root switches retain write, barrier, readback, and release behavior.

Execution is deferred by the explicit no-verification instruction.
