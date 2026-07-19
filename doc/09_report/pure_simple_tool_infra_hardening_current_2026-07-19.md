# Pure-Simple tooling hardening status — 2026-07-19

No row is release-qualified until an admitted current Stage 4 runs its listed
evidence. Rust-seed or stale deployed output is bootstrap/debug evidence only.

| Tool | Current status | Known bug or risk | Root solution / proving evidence |
|---|---|---|---|
| Test runner | Structured-evidence source fixed; deployment blocked | stdout could forge success; temporary Rust recovery passed examples then remained alive | canonical private evidence; stdout-only modes fail closed; pure-Simple Stage4 smoke must exit inside its hard wall |
| Lint | JSON/fix source fixed; runtime pending | mixed human/JSON output, coupled dry-run, missing-file and atomic-write failures could look green | JSONL-only mode, independent `--fix-dry-run`, canonical atomic write, public CLI contract |
| Formatter/fix | Expanded Core-C collision regression passed; native-all and Stage 4 pending | delete-before-rename could lose the original; missing provider and stale temp names could block writes | bounded exclusive-temp retry, exact binary replacement/cleanup regression, then native-all and Stage 4 integration |
| Duplicate checker | source and Core-C CLI-exit ABI fixed; runtime pending | terminal split artifact inflated windows; focused entry initially crashed on missing `rt_cli_exit`; unresolved entry-closure fallbacks still prevent an authoritative scan | canonical `lines()`, occurrence-set deduplication, Core-C exit alias, then above-threshold clean and exact-clone Stage 4 probes |
| Native build/cache | focused Rust source checks passed; rebuilt provider pending | timeout discarded safe partial work; cache key omitted effective backend/optimization | atomically retain only dependency-independent `no_mangle` objects; key by backend/opt; cold/fail/retry equivalence |
| Bootstrap admission | blocked on current Stage 4 | stale/seed/debug artifacts can give false confidence | provenance admission, exact candidate hash, bounded essential-tools smoke before deploy |
| `check` | investigation required | app path may stop at parse/policy and false-green HIR/type-invalid input | route through the canonical driver `check_file`; add one type-invalid regression |
| MCP server | native-first source exists; qualification pending | wrapper/registry can select stale or source fallback; startup/request budgets unproven | exact native artifact admission, stdio integration, warm startup/latency/RSS evidence |
| LSP MCP server | investigation required | reported child-process leak lacks an authoritative spawner trace | trace the real owner, fix once there, then lifecycle and RSS regression |
| SPipe/docgen | source/manual present; generated evidence blocked | argv/runtime crashes or stalls can prevent truthful manual generation | admitted runtime, bounded docgen, generated/manual parity and zero placeholders |
| Test daemon | existing owner; lifecycle evidence pending | stale lock/PID or orphan processes can wedge tests | bounded start/status/run/stop and stale-state recovery evidence |
| Essential-tools smoke | source hardened; execution blocked | absent timeout command ran unbounded; forged stdout and vacuous clean duplicate probe were not rejected | fail closed without `timeout`/`gtimeout`; calibrated runner/lint/duplication probes against exact Stage 4 |

## Next admission sequence

1. Produce one incremental Stage 4 candidate; do not run a full bootstrap.
2. Admit its provenance, then run the essential-tools aggregate once.
3. Run focused lint, duplication, atomic-provider, compiler/lib, MCP, and LSP MCP
   checks once each; generate the SPipe manual only after those pass.
4. Record command, candidate hash, exit, elapsed time, and max RSS, then review,
   sync, and push.
