<!-- codex-research -->
# SSpec Documentization Maintenance Local Research — TLDR

```sdn
owners = flow(
  spipe_parser_docgen -> sspec_documentization_analyzer,
  easy_fix -> preview_confirm_apply,
  existing_spipe_lint -> referenced_not_duplicated
)
```

- `simple spipe-docgen` is canonical; its current “coverage” is only a raw
  documentation-line score and cannot explain professional quality.
- Existing `SPIPE001..007` already own placeholder/assertion correctness.
- `simple duplicate-check` supplies the best scope/output/threshold precedent.
- EasyFix supplies replacements, confidence, conflict checks, and atomic apply;
  the new command must preview by default and require explicit apply/confirm.
- The anti-pattern guide supplies twelve concrete documentization rule inputs.
- Selected scenario-manual requirements already own captures, audiences,
  troubleshooting, keymaps, and traceability; consume rather than redefine.
- Bootstrap-era Markdown-to-SSpec tools are dormant and weakly tested; port
  ideas into pure Simple and emit fail-fast TODO assertions.
- `spec-gen`, old `doc/spec_gen`, and `feature-doc` overlap/confuse; do not add
  another generator. Canonicalize maintenance around SPipe.
- Refactor/system-test/sp_dev skills, Claude/Gemini instructions, the template,
  LLM wiki, and manual guide all require synchronized updates after selection.
