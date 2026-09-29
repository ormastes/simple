# REQ-019 repository migration checker

The executable scenario creates one exact legacy raw-runtime finding and a
reviewed baseline entry. It proves the untouched row emits an actionable
warning, the exact unchanged fingerprint classified as a changed path errors
immediately, a moved signature errors, and the
configured `1.0.0` release epoch promotes the finding and non-empty baseline to
errors. The receipt also exposes bounded scan throughput and confirms a single
file-inventory process.

Executable source:
`test/03_system/runtime/mcdc_hal_migration_checker_spec.spl`.
