# MC/DC and `rt(hal)` migration checker

`scripts/audit/mcdc_hal_migration_check.spl` is the Pure Simple owner for
REQ-019. It makes new or changed missing-assurance, forbidden-allocation, and
obsolete-interface findings errors immediately. Only an exact untouched
fingerprint in `scripts/audit/baselines/mcdc-hal-migration-v1.sdn` may warn.
Every warning prints its owner, concrete fix, and exact removal deadline.

Run it from the repository root:

```sh
bin/simple run scripts/audit/mcdc_hal_migration_check.spl
```

The reviewed policy is `config/check/mcdc_hal_migration.sdn`. The default
development epoch is `1.0.0-RC`; the next exact release epoch is `1.0.0`.
Passing `--epoch 1.0.0` promotes every finding repository-wide, requires an
empty baseline, and requires every compatibility shim listed in
`mcdc-hal-compat-shims-v1.sdn` to be removed. A moved or edited violation has a
new fingerprint and errors; stale, duplicate, malformed, unowned, or
deadline-free debt also errors. There is deliberately no record/update mode.

The checker performs one bounded file-inventory process and reads each admitted
source file once in the policy scan. File count, per-file bytes, aggregate
source bytes, command output, baseline bytes, and finding count are capped.
Changed paths are indexed once, so even an unchanged fingerprint on a changed
path is an immediate error. Findings, baseline fingerprints, and changed paths
are joined through bounded exact-key maps in expected linear time rather than
through quadratic repeated scans. Its final receipt reports scan microseconds,
files, bytes, files/second, file reads, and inventory-process count. Collect
whole-process wall time and peak RSS once with:

```sh
bin/simple run scripts/check/mcdc_hal_migration_performance.spl
```

Override `--repo`, `--config`, `--baseline`, `--shims`, `--base`,
`--changed-file`, or `--epoch` only for an isolated fixture or reviewed release
gate. CI should use the default base ref so committed changes, working-copy
changes, and untracked files are all classified as changed.
