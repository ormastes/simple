# Server context nonfunctional requirements

NFR-001: Strict SDN <=64 KiB; at most sixteen servers and contexts. Negative
specs must exercise limits, duplicates, unknown fields and dangling references.

NFR-002: No raw secrets, shell task interpolation, host-key bypass, implicit
network probing or fallback from rejected remote transport to local execution.

NFR-003: One SSH request process with bounded input/output and retained lease
until confirmed collection; no mutation retries after uncertain transport.

NFR-004: Measure warm startup, representative request latency and peak RSS on
LinuxPodman and WindowsDocker clients using the admitted self-hosted runtime.
No runtime measurements or cross-host qualification are currently available.
