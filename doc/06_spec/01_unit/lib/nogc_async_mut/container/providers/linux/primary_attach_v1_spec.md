# Primary attach leaf planning and eligibility

AUTHORED / NOT_RUN. Five pure scenarios; no native process or handles.

- Independent exact attach argv: stdin enabled, signal proxy false, detach keys disabled, full CID; typed container-only eligibility query.
- Distinct primary-attach root and canonical daemon template, CPU/memory, observed executable digest, zero admission fields and normalized digest.
- Matching running stdin/TTY configuration; wrong terminal/containment refused.
- Every runtime label/ID mismatch, closed stdin, nonrunning primary and request mismatch refused.
- Duplicate/unknown/nested/trailing/type-invalid/oversized JSON refused.

Podman v5.2.5 inspect producer ef4bac... maps Config.OpenStdin from retained Stdin and Config.Tty from OCI process Terminal. Attach documentation 7a4ab... specifies empty detach keys disable them. These are eligibility configuration facts, not PID/native ownership or permission to write input/resize. Shared verified admission and the canonical owned group transport remain required; no reader or registry is introduced.
