<!-- codex-design -->
# SSpec Documentization Maintenance Architecture — TLDR

```sdn
cli -> sspec_maintain -> [analyzer, report, cache, improve, scaffold, documentize]
improve -> easy_fix
documentize -> spipe_docgen
analyzer -> existing_spipe_lint
```

- Dedicated pure-Simple capsule; CLI/MCP are thin adapters.
- Stable report model with seven weighted components; blockers cap effective
  aggregate at 49 without hiding component evidence.
- Per-source/manual-pair cache includes normalized path, content,
  rules/config/tool; unchanged directory siblings reuse cached analysis;
  `--no-cache` preserves report semantics.
- Preview-first EasyFix path: hash, in-memory patch, confirm, rollback artifact,
  atomic write, then one reparse/check.
- Reference scaffolding preserves IDs/source hash and leaves unknown behavior as
  explicit failing TODO assertions.
- SPipe remains the only canonical manual generator; maintenance uses isolated
  content-addressed staging, then adds observed score/findings appendices
  without invented prose or intermediate repository overwrites.
- Existing `spipe-docgen`, SSpec, and `SPIPE001..007` stay compatible.
