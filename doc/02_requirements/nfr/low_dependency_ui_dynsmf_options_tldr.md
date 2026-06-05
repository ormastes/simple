# Low Dependency UI dynSMF NFR Options TLDR

- NFR-A: static dependency gates, low-medium effort.
- NFR-B: runtime load/unload evidence, medium effort.
- NFR-C: startup/RSS budgets, medium-high effort.
- Recommended first tranche: NFR-A plus NFR-B.

```sdn
nfr_options {
  static_import_gate
  runtime_load_evidence
  startup_rss_budget
}
```
