# CLI surface drift fail-closes completion to `[]`, blocking startup-perf C4

- **Filed:** 2026-09-05
- **Status:** OPEN
- **Blocks:** `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md`
  Phase C checkbox C4, pinned by
  `test/03_system/plan_acceptance/startup_perf_plan_spec.spl`
  "REMAINING — C4 help/completion generator from SCI + migration report ...".

## Symptom

The C4 oracle asserts

```
expect(cli_surface_completion_candidates_v1(snapshot, "bu"))
    .to_equal(["bug-add", "bug-gen", "bug-resolve", "build"])
```

and measures `[]`. The empty list is **not** an empty snapshot — it is a
fail-closed refusal.

## Mechanism

`cli_surface_completion_candidates_checked_v1`
(`src/app/cli/help_surface_report.spl:103`) only emits candidates when BOTH
`cli_surface_exact_help_dispatch_parity_v1(snapshot)` and
`source_hashes_current` hold. The second comes from
`cli_surface_generated_sources_current_v1`
(`src/app/cli/help_surface_inventory.spl:91`), which compares the committed
identity receipt in `src/app/cli/help_surface_generated_data.spl` against the
live sources. **All four bound hashes are stale** (measured 2026-09-05,
`shasum -a 256`):

| source | committed constant | actual |
|---|---|---|
| `src/app/cli/_CliMain/main_and_help.spl` | `36016a94…` | `6f2285d0…` |
| `src/app/cli/command_registry.spl` | `886b29d2…` | `fab45d8b…` |
| `src/app/cli/dispatch/table.spl` | `4bc56480…` | `b1921f39…` |
| `src/app/cli/_CliMain/args_and_os_commands.spl` | `3e436344…` | `46a49030…` |

So completion correctly refuses to answer from a receipt that no longer
describes the tree. **The receipt cannot simply be regenerated**: the sanctioned
generator refuses first.

```
$ src/compiler_rust/target/debug/simple run src/app/cli/help_surface_codegen.spl
cli_help_surface_codegen=FAIL detail=dispatch-registry-drift
```

## Root cause — the three command sets have genuinely diverged

Measured 2026-09-05 by probing the same functions the generator uses
(`cli_surface_codegen_extract_dispatch_v1`, `cli_registry_command_names_v1`,
`get_all_commands`):

```
counts dispatch=124 registry=123 table=87
dispatch-only  (1): [perf]
registry-only (vs dispatch) (0): []
table-only    (vs registry) (3): [cs, perf, tags]
registry-only (vs table)   (39): [agents, browser, cache, check-arch,
  counterpart, dap, debug-ui, desugar, diagram, doc-coverage, env,
  grammar-doc, ide, ios, jj, js, launch-meta, leak-check, lex, lock, log,
  lsp, mem, office, optimize, os, pkg, plugin, saml, sbom, snpm, stats, t32,
  task-daemon, test-daemon, theme-sync, ui, update, watch-daemon]
```

`_codegen_validate_canonical_inputs_v1` (`help_surface_codegen.spl:199`)
requires `dispatch == registry` **and** `table == registry`. Two distinct
drifts must be closed before the receipt can be regenerated:

1. **`dispatch-registry-drift`** — `perf` is dispatched in `main_and_help.spl`
   but is absent from the canonical registry. One command.
2. **`table-registry-drift`** — the dispatch table carries 87 of the registry's
   123 commands; 39 registry commands have no table row, and `cs`, `perf`,
   `tags` have a table row with no registry entry. 42 differences.

Fixing (1) alone does not unblock the box; the generator then stops at (2).

## Why this was not fixed in the 2026-09-05 plan-acceptance pass

Reconciling 42 commands between the canonical registry and the live dispatch
table is a CLI-surface project in its own right, and every candidate edit is on
the path that dispatches every `simple` subcommand. It is not a safe drive-by
inside an acceptance-spec session. Each of the 39 registry-only commands must be
decided individually: does it need a real table row, or is the registry entry
itself stale and the command genuinely retired?

## Next step

Decide the 42 rows, land the reconciliation, then run
`src/compiler_rust/target/debug/simple run src/app/cli/help_surface_codegen.spl --write`
to regenerate the identity receipt. Do **not** hand-edit the sha256 constants in
`help_surface_generated_data.spl` — the generation-id check
(`_codegen_generation_id_v1`) binds them together and a hand-patched receipt
would re-open exactly the fail-open this guard exists to prevent.
