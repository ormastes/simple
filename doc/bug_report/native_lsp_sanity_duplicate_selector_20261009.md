# Reviewed LSP native sanity duplicates the launcher selector

The Phase1 LSP native build produced binary SHA256
`625fa9e7b27f18e3e6fc87c25a5bcb1f8fd4fd057c6253e7aeab585b47b11e0e`.
Its original reviewed version probe failed with stdout mismatch, exit 0 and
empty output. Original evidence remains under
`/home/ormastes/simple-linux-bootstrap-build-20261009/phase-matrix-plan/phase1-verification/logs/lsp_build.sanity.OTKKK0`.

The harness invoked `simple_lsp_mcp_server simple_lsp_mcp_server --version`.
The native server already recognizes its executable name in argv0, so the
extra selector becomes the first user argument. That bare argument selects
stdio mode; EOF then exits cleanly without printing the version. The expected
version output is legitimate, and the seed's native-build capability is not
unsupported.

The corrected probe omits the selector for the canonical basename. Renamed
artifacts retain their explicit selector; other platform spellings retain the
existing behavior. Source and binary hash checks, timeout, process containment,
and exact stdout/stderr/exit comparisons remain intact.

The subprocess regression exercises the production harness's canonical and
renamed argument forms against exact argument-accepting executable fixtures.
It also confirms that the unqualified MCP role does not invoke a binary with
the LSP version oracle. Previously passing MCP checks were not rerun.

The existing Phase1 LSP artifact passed the corrected actual guarded probe:
exact stdout `simple-lsp-mcp 0.9.8`, empty stderr and exit 0. Receipt:
`/home/ormastes/wsl-native-phase4-plan/phase1-lsp-version-corrected-configured/run/sanity.env`.
The initial standalone corrected attempt lacked the required centralized
TMPDIR and failed process admission; that separate receipt remains preserved.
This is a version sanity PASS, not full LSP behavior or release qualification.
