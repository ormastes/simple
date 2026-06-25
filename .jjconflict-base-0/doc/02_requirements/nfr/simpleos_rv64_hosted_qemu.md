<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU NFRs

- NFR-RV64-HOSTED-001: The hosted lane must fail within 120 seconds when SSH or HTTP reachability is missing.
- NFR-RV64-HOSTED-002: Host-side diagnostics must identify which hosted proof stage failed: serial preflight, TCP open, SSH banner, or HTTP response.
- NFR-RV64-HOSTED-003: The smoke lane must not emit desktop process-backed markers for RV64 until the underlying kernel/VFS/process path is real.
