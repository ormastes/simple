<!-- codex-architecture -->
# MC/DC + HAL Hardening — TLDR

Purpose: complete compiler-wide MC/DC and safe Pure/C/Rust HAL comparison with mission-critical memory and performance guarantees.

```text
HIR manifests -> MIR Begin/Condition/Commit -> static direct | dynamic slots
       |                                           |
       +-> fixed receipts -> proof analyzer <- parent merge
rt(hal) manifest -> isolated provider processes -> env plans -> one parent commit
```

- Static-off removes every probe, payload, symbol, section, and dynload edge.
- Static-on writes one fixed record per decision evaluation.
- Dynamic mode uses canonical aspect packs and ordered R/W data-cell publication.
- MC/DC prefers unique cause; masking requires a Boolean-DAG proof.
- `rt(hal)` defaults to Critical; critical closures allocate nothing after `seal()`.
- Pure/C/Rust providers are process-isolated and return bounded receipts.
- Effectful providers plan; the parent performs one interaction and replays it.
- Only capability/fixture/platform/safety/nondeterminism exclusions are allowed.
- New/changed migration findings error now; untouched legacy warns until the next release.
- Cache keys include content/catalog/ABI/generation; size-only freshness is forbidden.

Next: `doc/05_design/mcdc_hal_runtime_hardening.md`, `doc/03_plan/sys_test/mcdc_hal_runtime_hardening.md`.

