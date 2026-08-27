# REQ-019 migration-gate performance receipt (2026-08-22)

Scope: the configured production MC/DC, HAL, environment-instruction, and
native runtime-I/O roots in `config/check/mcdc_hal_migration.sdn`.

## Complexity and memory review

- Source traversal is one bounded inventory process plus one read and one
  line scan per admitted file: `O(files + source bytes + findings)`.
- Finding/baseline/changed membership uses dictionaries. This change removes
  the remaining linear changed-path duplicate probe, avoiding `O(changes^2)`.
- The only ordering work is one bounded startup sort of paths; no sort,
  allocation, copy, subprocess, or dynamic dispatch is added to runtime/HAL
  request paths. The gate is compile/repository-check time only.
- Limits remain fail-closed: 256 files, 1 MiB/file, 16 MiB total source, and
  2,048 findings. Vendored headers and runtime test fixtures are outside the
  canonical roots.

## Host evidence

Host inventory of all configured roots (36 files), using the same single
`find` shape as the checker:

```text
inventory_wall_seconds=0.01
inventory_peak_rss_kb=4096
```

The routing/exclusion negative self-test:

```text
STATUS: PASS mcdc-hal-migration-gate self-test
gate_selftest_wall_seconds=0.05
gate_selftest_peak_rss_kb=2304
```

The source-matched Pure Simple checker timing could not be refreshed in this
worktree: `bin/simple` is absent, and the available deployed compiler was
already classified inadmissible for acceptance. Per bootstrap policy, no Rust
seed or cross-worktree binary was substituted. The retained performance runner
will emit wall time, peak RSS, scan microseconds, file count, source bytes,
read count, and inventory-process count when an admitted runtime is deployed.
