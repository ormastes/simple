<!-- codex-design -->
# Bootstrap compiler/backend stage split NFRs

- Stage 4 must compile zero files under `src/compiler/**`.
- ABI, source, interface, archive, or runtime mismatch fails before tool compilation.
- Tooling-only output must be reproducible from one Stage-3 manifest.
- Tooling-only and audit-full builds pass identical CLI and essential-tool gates.
- Every stage retains timing, RSS, compiled/reused counts, and artifact hashes.
