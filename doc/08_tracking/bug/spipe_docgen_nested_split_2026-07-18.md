# SPipe docgen nested `str.split` resolution failure

Date: 2026-07-18

## Reproduction

```text
bin/simple spipe-docgen \
  test/03_system/app/llm_caret/feature/llm_caret_spipe_infra_access_hardening_spec.spl \
  --output doc/06_spec/03_system/app/llm_caret/feature --no-index
```

After loading the generator and beginning `Processing specs`, the deployed
self-hosted compiler reports:

```text
error: semantic: method 'split' not found on value of type str in nested call context
```

No Markdown file is produced. The feature uses the repository-supported manual
companion path so executable specs remain outside `doc/06_spec`.

## Acceptance

- The command above completes without a grammar workaround in the feature spec.
- The generated document contains the source documentation block, all scenario
  names, and every `step("...")` string.
- Existing docgen fixtures remain green.

## Revived-lane status (2026-07-18)

Current `origin/main` includes the string `split` static-lowering fix
(`b243e5e1578`) and the recovered spec retains its original grammar. Runtime
acceptance remains blocked because the fresh canonical bootstrap passed Stage 3
but its full-CLI Stage 4 was terminated by SIGTERM (exit 143). Docgen was not
rerun through a bootstrap-only seed and the manual companion remains explicitly
manual.
