<!-- codex-research -->
# SSpec Documentization Maintenance NFR — TLDR

```sdn
nfr = contract(
  deterministic = true,
  warm_file_p95_ms = 500,
  thousand_specs_seconds = 30,
  max_rss_mib = 384,
  writes = "atomic + rollback + idempotent"
)
```

- Byte-identical machine reports/scaffolds for identical inputs.
- Incremental cache with precise create/edit/move/delete/manual/rule invalidation
  and `--no-cache` parity.
- Pure human/JSON/SARIF serializers, stable fingerprints and baselines.
- Preview performs no writes; explicit apply is atomic, recoverable, and
  idempotent; smallest verification runs once.
- Fully offline core; future LLM help is opt-in preview-only and never changes
  deterministic scoring.
- Preserve existing SSpec, `spipe-docgen`, and `SPIPE001..007` compatibility.
- Cohesive <=800-line modules, bounded hot paths, diagnostics off machine stdout,
  >=80% branch target, and professional zero-stub generated manual review.
