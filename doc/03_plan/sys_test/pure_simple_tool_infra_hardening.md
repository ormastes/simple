# Pure-Simple tool and infrastructure hardening system-test plan

## Scope

The canonical executable spec is
`test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl`.
Its generated manual mirrors to
`doc/06_spec/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.md`.

## Scenarios

1. Admit a non-seed runtime and reject seed/debug identities.
2. Preserve red, empty, nonzero-child, timeout, and sibling execution outcomes.
3. Bypass the serial daemon for nested tests.
4. Reject hostile duplicate-check paths without shell side effects.
5. Honor scoped multi-name lint attributes through the canonical parser.
6. Derive dispatch inventory from the command table.
7. Select cached native MCP/LSP artifacts and reject source/seed fallback.
8. Prove daemon cache hit/miss equivalence and invalidation.
9. Prove checker and `gen-lean` terminate within deadlines.
10. Measure warm CLI/test/MCP/LSP latency and max RSS against selected NFRs.

## Test levels

- Unit: outcome classifier, output parsing, lint attributes, file selection.
- Integration: runner child/daemon routing, launcher candidate selection.
- System: production command/wrapper paths and retained performance evidence.

## Stop rules

Each acceptance command runs once per session. A failing production provenance
probe blocks performance claims but not static/unit fixes. Maximum three
verify/fix cycles; no repeated green checks.
