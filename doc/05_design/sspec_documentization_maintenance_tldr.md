<!-- codex-design -->
# SSpec Documentization Maintenance Design — TLDR

```sdn
report = {
  score: seven_components + raw/effective,
  findings: stable_SSDOC_ids + locations + fingerprints + fixes,
  outputs: [human, json, sarif]
}
```

- Initial rules cover narrative, steps/names, oracle blockers, traceability,
  evidence, behavioral gaps, mirror freshness, folding/tags, and invalid `@step`.
- Default scan is advisory; score/severity policies independently decide exit.
- Cache stores the report model; baseline classifies new/unchanged/resolved.
- Safe improvements are exact mechanical EasyFixes only; preview, confirm,
  rollback artifact, atomic write, parser+lint once.
- Scaffold extracts explicit Markdown REQs/normative sections, preserves source
  line/hash, and emits explicit failing TODO assertions for unknown behavior.
- Documentize runs canonical SPipe, re-analyzes the mirror, and idempotently adds
  a delimited score/findings appendix.
- Usage=2, operation=1, policy=3, success=0; machine errors stay machine-pure.
