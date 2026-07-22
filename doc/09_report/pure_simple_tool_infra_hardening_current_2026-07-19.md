# Pure-Simple tooling hardening status — 2026-07-19

No row is release-qualified until an admitted current Stage 4 runs its listed
evidence. Rust-seed or stale deployed output is bootstrap/debug evidence only.

| Tool | Current status | Known bug or risk | Root solution / proving evidence |
|---|---|---|---|
| Test runner | Structured evidence, indexed-u8 failure gate, and opt-in-only SPipe docgen fixed in source; seed/source MCP stdio spec exits 0 | self-hosted Stage 4 qualification pending; source launch emits excessive parser recovery diagnostics; a live unrelated PID is accepted as daemon readiness | admit an incremental Stage 4, then suppress recovery noise and add bounded daemon readiness ping |
| Lint | style strictness, query AST-dispatch, and invalid-profile false-greens fixed in source; Stage 4 qualification pending | production `simple lint` still omits semantic AST leaf checks; mixed output/dry-run/atomic risks remain | adapt shared AST leaves into typed `LintResult` values, prove CLI/query code parity, then qualify bounded strict probes on admitted Stage 4 |
| Formatter/fix | `FixApplicator` failed-write false-green fixed and directly exercised; formatter `--write` now uses the canonical atomic provider; MCP stdio regression exits 0; Stage 4 integration pending | standalone accessor and bare-import migration fixers still write non-atomically | make standalone fixers fail closed through the canonical atomic writer; qualify all consumers on the admitted Stage 4 runtime |
| Duplicate checker | missing-target, malformed-option, and invalid mode/format false-greens fixed in source; Stage 4 runtime pending | unresolved entry-closure fallbacks block authoritative scan qualification | keep explicit help at 0 and qualify the bounded clean/found/invalid fixtures on admitted Stage 4 |
| Native build/cache | monitor classification and the core-C `trim_start`/fail-closed fork-hook link gaps are fixed in source; focused runtime contract passes | incremental Stage 4 candidate, cache, Mach-O/COFF, and alias qualification remain | finish the active cached Stage 4 replay; keep cache/backend keys and alias sections isolated |
| Bootstrap admission | blocked: settled incremental Stage 4 timed out at 1200s with no candidate; 222 MiB/2,713-file cache retained | later trace evidence reaches 40 files and stalls while parsing `lexer_struct.spl`; current source has closure dedup and phase receipts but they are not yet in an admitted runtime | refresh only the staged compiler artifacts needed for current tracing, then run one cache-preserving replay with phase/closure tracing; require provenance, exact hash, and bounded essential-tools smoke before deploy |
| Pure-Simple runtime ABI | `trim_start` is implemented and admitted by the required-symbol contract | the broader value/memory probe exits 91 at the existing dictionary-entry row-shape assertion | fix `core_values.spl` dictionary-entry construction, then rerun the existing exact probe once |
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
