# SCV Migration Month Plan — TL;DR

Full plan: `scv_migration_month_plan.md`. Ledger: `.spipe/scv-migration/todo.sdn`.
Ceiling for the month is **S4 dual-write**; SCV never becomes authoritative here.

```text
2026-08-25        09-01          09-08          09-15          09-25
  |  W1 S0→S1     |  W2 S1→S2    |  W3 S2→S3    |  W4 S3→S4    |
  | MIG-01..08    | MIG-09..14   | MIG-15..20   | MIG-21..25   |
  | ChangeId      | fsck+        | tree agree   | quarantine GC|
  | checkpoint    | journal/WAL  | shadow repl  | recover x5   |
  | doctor        | rebuild-db   | bundles      | restore drills|
  | verify-bknd   | fmt versions | crash harness| dual-write cmp|
  | fault hook    | ro adapter   | FileBuffer   | S4 review    |
  | lint+alloc    | S2 drill     | S3 review    | (30-day clock)|
  | PQ signing    |              |              |               |
  | ledger/timer  |              |              |               |

  hourly: check-scv-migration-todo.shs
     ledger step due? -> verify-script.shs (PQ sig) --fail--> blocked/unsigned
                                          --PASS--> timeout sh steps/SCV-MIG-NN.shs
                                                    last line PASS -> done
```

Commands:
- `sh scripts/check/check-scv-migration-todo.shs [--dry-run] [--now UTC]`
- `sh scripts/trust/sign-script.shs --name scv-migration-root scripts/scv-migration/steps/SCV-MIG-NN.shs`
- `sh scripts/setup/install-scv-migration-timer.shs --check|--apply|--remove`
