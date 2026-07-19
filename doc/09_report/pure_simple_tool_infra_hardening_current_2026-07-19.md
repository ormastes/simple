# Pure-Simple tooling hardening status — 2026-07-19

No row is release-qualified until an admitted current Stage 4 runs its listed
evidence. Rust-seed or stale deployed output is bootstrap/debug evidence only.

| Tool | Current status | Known bug or risk | Root solution / proving evidence |
|---|---|---|---|
| Test runner | Structured evidence, indexed-u8 failure gate, and opt-in-only SPipe docgen fixed in source; seed/source MCP stdio spec exits 0 | self-hosted Stage 4 qualification pending; source launch emits excessive parser recovery diagnostics; a live unrelated PID is accepted as daemon readiness | admit an incremental Stage 4, then suppress recovery noise and add bounded daemon readiness ping |
| Lint | style strictness and query AST-dispatch false-greens fixed in source; Stage 4 qualification pending | production `simple lint` still omits semantic AST leaf checks; mixed output/dry-run/atomic risks remain | adapt shared AST leaves into typed `LintResult` values, prove CLI/query code parity, then qualify bounded strict probes on admitted Stage 4 |
| Formatter/fix | `FixApplicator` failed-write false-green fixed and directly exercised; MCP stdio regression exits 0; Stage 4 integration pending | formatter `--write` still uses checked but delete-first `file_write` | route formatter through the canonical atomic writer; qualify both consumers on the admitted Stage 4 runtime |
| Duplicate checker | missing-target and unknown/malformed-option false-greens fixed in source; Stage 4 runtime pending | invalid enum values such as `--mode tokne` still silently retain semantic mode; unresolved entry-closure fallbacks block authoritative scan qualification | validate mode/format values before scanning, keep explicit help at 0, and use bounded calibrated fixtures for qualification |
| Native build/cache | focused Rust source and ELF alias-GC link checks passed; Mach-O/COFF alias projection and rebuilt provider pending | resource monitor substring-matches `test_runner_new` and kills native builds as tests; focused core-C runner link lacks hosted symbols; cache and alias risks remain | classify the command token in the monitor; use canonical cached Stage 4 replay; keep cache/backend keys and alias sections isolated |
| Bootstrap admission | blocked on current Stage 4 | stale/seed/debug artifacts can give false confidence | provenance admission, exact candidate hash, bounded essential-tools smoke before deploy |
| `check` | HM expression-bodied return false-positive fixed; CLI false-green remains | both workers stop at parse/policy; explicit `return` still lacks HM expected-return context, so fatal routing is not yet safe for the broader corpus | implement explicit-return inference, prove paired reject/positive CLI exits, then make HM fatal only in canonical Check mode and route both workers through its internal owner |
| MCP server | native-first source exists; qualification pending | wrapper/registry can select stale or source fallback; startup/request budgets unproven | exact native artifact admission, stdio integration, warm startup/latency/RSS evidence |
| LSP MCP server | diagnostics uses group-aware bounded execution; current native smoke fails | list-only wrapper admission accepts an artifact whose real `lsp_symbols` call fails; current smoke lists 11 tools but fails framing, correlation, schema, and call checks | restore a correlated bounded `tools/call` admission probe, invalidate stale stamps, then rerun native smoke |
| SPipe/docgen | source/manual present; generated evidence blocked | argv/runtime crashes or stalls can prevent truthful manual generation | admitted runtime, bounded docgen, generated/manual parity and zero placeholders |
| Test daemon | absolute-expiry protocol fixed and unit-tested; Stage 4 lifecycle/ownership evidence pending | old path-only requests could let a fixed 600s daemon child outlive its client and block later work; production CLI and session client still use inconsistent owners/protocols | tagged absolute expiry, dequeue-time spawn refusal, and remaining-time group-aware execution; then reconcile CLI owner and prove start/status/run/stop plus stale-state recovery |
| Essential-tools smoke | source hardened; execution blocked | absent timeout command ran unbounded; forged stdout and vacuous clean duplicate probe were not rejected | fail closed without `timeout`/`gtimeout`; calibrated runner/lint/duplication probes against exact Stage 4 |

## Next admission sequence

1. Produce one incremental Stage 4 candidate; do not run a full bootstrap.
2. Admit its provenance, then run the essential-tools aggregate once.
3. Run focused lint, duplication, atomic-provider, compiler/lib, MCP, and LSP MCP
   checks once each; generate the SPipe manual only after those pass.
4. Record command, candidate hash, exit, elapsed time, and max RSS, then review,
   sync, and push.
