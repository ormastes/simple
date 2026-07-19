# Pure-Simple tooling hardening status — 2026-07-19

No row is release-qualified until an admitted current Stage 4 runs its listed
evidence. Rust-seed or stale deployed output is bootstrap/debug evidence only.

| Tool | Current status | Known bug or risk | Root solution / proving evidence |
|---|---|---|---|
| Test runner | Structured-evidence and shared sdoctest config dispatch fixed; deployment blocked | stdout could forge success; temporary Rust recovery passed examples then remained alive; inline ignore arrays called a nonexistent prefix helper | canonical private evidence; stdout-only modes fail closed; bracketed ignore-array regression; pure-Simple Stage4 smoke must exit inside its hard wall |
| Lint | style `--warn-all --deny-all` false-green fixed in source; Stage 4 qualification pending | ST001-3 were left at built-in Allow; STUB002 still shares deny-level `stub_impl` policy; mixed output/dry-run/atomic risks remain | preserve default style Allow, promote it only when configured Warn, run the focused ST001 regression, then qualify the bounded strict probes on admitted Stage 4 |
| Formatter/fix | Core-C and native-all provider regressions passed; Stage 4 integration pending | delete-before-rename could lose the original; missing provider and stale temp names could block writes | bounded exclusive-temp retry, exact binary replacement/cleanup regressions, then Stage 4 integration |
| Duplicate checker | missing/flags-only target false-green fixed in source; Stage 4 runtime pending | implicit full-src semantic default was hang-prone; unresolved entry-closure fallbacks still block authoritative scan qualification | lightweight target parsing now requires a positional path, explicit help stays 0, and bounded calibrated fixtures remain the qualification path |
| Native build/cache | focused Rust source and ELF alias-GC link checks passed; Mach-O/COFF alias projection and rebuilt provider pending | timeout discarded safe partial work; cache key omitted effective backend/optimization; method-owner changes retained stale dependents; compatibility aliases shared one section and pulled unreachable targets into strict links | atomically retain only dependency-independent `no_mangle` objects; key by backend/opt; isolate alias sections; add Mach-O/COFF projection gates; use isolated shards after owner changes; cold/fail/retry equivalence |
| Bootstrap admission | blocked on current Stage 4 | stale/seed/debug artifacts can give false confidence | provenance admission, exact candidate hash, bounded essential-tools smoke before deploy |
| `check` | HM expression-bodied return false-positive fixed; CLI false-green remains | both workers stop at parse/policy; explicit `return` still lacks HM expected-return context, so fatal routing is not yet safe for the broader corpus | implement explicit-return inference, prove paired reject/positive CLI exits, then make HM fatal only in canonical Check mode and route both workers through its internal owner |
| MCP server | native-first source exists; qualification pending | wrapper/registry can select stale or source fallback; startup/request budgets unproven | exact native artifact admission, stdio integration, warm startup/latency/RSS evidence |
| LSP MCP server | diagnostics uses group-aware bounded execution; server leak attribution/lifecycle still unproven | the 48-process report lacks PID/PPID/stdin-owner evidence and current server exits on EOF | 10s/1MiB diagnostics bound with descendant cleanup; capture the external client owner and add tracked-PID EOF lifecycle regression |
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
