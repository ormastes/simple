# Print Log Policy Spec

Source: `test/unit/compiler/parser/print_log_policy_spec.spl`

## Scenarios

- Parser source wires non-script bare `print` handling through `parser_warn_print_if_needed`.
- The warning text is `LOG001: use log() instead of print() in non-script code`.
- Statement-level and module-level bare `print` paths both call the warning hook.
- Script paths remain exempt through `parser_path_is_script`.

This spec verifies source wiring because the current parser-entry unit specs cannot import `parser_init` in the release runner.

## Reproduction

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/parser/print_log_policy_spec.spl --mode=interpreter --no-cover-check
```
