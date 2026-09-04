<!-- codex-design -->
# Windows ConPTY for SMUX NFRs

- NFR-001: PTY reads honor their timeout without a busy wait.
- NFR-002: handles and child processes are closed exactly once.
- NFR-003: no Unix behavior regression.
- NFR-004: Windows shell selection uses the platform environment with a stable fallback.
