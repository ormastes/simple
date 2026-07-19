# Pure-Simple tooling hardening status — 2026-07-19

No row is release-qualified until an admitted current Stage 4 runs its listed
evidence. Rust-seed or stale deployed output is bootstrap/debug evidence only.

| Tool | Current status | Known bug or risk | Root solution / proving evidence |
|---|---|---|---|
| Test runner | Structured-evidence and shared sdoctest config dispatch fixed; deployment blocked | stdout could forge success; temporary Rust recovery passed examples then remained alive; inline ignore arrays called a nonexistent prefix helper | canonical private evidence; stdout-only modes fail closed; bracketed ignore-array regression; pure-Simple Stage4 smoke must exit inside its hard wall |
| Lint | strict Core-C entry links and clean input passes; strengthened deny execution pending | mixed human/JSON output, coupled dry-run, atomic failures, and missing pure-Simple `strip` alias dispatch could look green or crash | JSONL-only mode, independent `--fix-dry-run`, canonical atomic write, `strip`/`trim` parity, plus added bounded `T001` + `STUB003` deny probe |
| Formatter/fix | Core-C and native-all provider regressions passed; Stage 4 integration pending | delete-before-rename could lose the original; missing provider and stale temp names could block writes | bounded exclusive-temp retry, exact binary replacement/cleanup regressions, then Stage 4 integration |
| Duplicate checker | source, Core-C CLI-exit ABI, and pure-Simple math owner fixed; Stage 4 runtime pending | terminal split artifact inflated windows; focused entry initially crashed on missing `rt_cli_exit` and `rt_math_sqrt`; unresolved entry-closure fallbacks still prevent an authoritative scan | canonical `lines()`, occurrence-set deduplication, Core-C exit alias, simple-core math/archive symbol gate, then above-threshold clean and exact-clone Stage 4 probes |
| Native build/cache | focused Rust source and ELF alias-GC link checks passed; Mach-O/COFF alias projection and rebuilt provider pending | timeout discarded safe partial work; cache key omitted effective backend/optimization; method-owner changes retained stale dependents; compatibility aliases shared one section and pulled unreachable targets into strict links | atomically retain only dependency-independent `no_mangle` objects; key by backend/opt; isolate alias sections; add Mach-O/COFF projection gates; use isolated shards after owner changes; cold/fail/retry equivalence |
| Bootstrap admission | blocked on current Stage 4 | stale/seed/debug artifacts can give false confidence | provenance admission, exact candidate hash, bounded essential-tools smoke before deploy |
| `check` | confirmed false-green; fix pending | both pure-Simple workers stop at parse/policy; canonical Check mode reaches HIR but HM errors remain warn-only; the documented fatal pass is absent | restore gated fatal HM diagnostics and reject/positive corpus first, then route both workers through canonical `check_file`; retain the existing type-invalid CLI regression |
| MCP server | native-first source exists; qualification pending | wrapper/registry can select stale or source fallback; startup/request budgets unproven | exact native artifact admission, stdio integration, warm startup/latency/RSS evidence |
| LSP MCP server | server leak attribution unproven; diagnostics descendant risk confirmed | the 48-process report lacks PID/PPID/stdin-owner evidence and current server exits on EOF; opt-in diagnostics timeout kills only its direct child | capture the external client owner; add tracked-PID EOF lifecycle regression; route diagnostics through group-aware bounded execution |
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
