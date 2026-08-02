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
- Content-addressed report cache includes source/manual/rules/config/tool;
  sorted single enumeration; `--no-cache` parity.
- Preview-first EasyFix path: hash, in-memory patch, confirm, rollback artifact,
  atomic write, then one reparse/check.
- Reference scaffolding preserves IDs/source hash and leaves unknown behavior as
  explicit failing TODO assertions.
- SPipe remains the only canonical manual generator; maintenance adds observed
  score/findings appendices without invented prose.
- Existing `spipe-docgen`, SSpec, and `SPIPE001..007` stay compatible.
