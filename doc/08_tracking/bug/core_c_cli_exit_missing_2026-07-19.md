# Core-C CLI exit was missing

- **Status:** fixed; focused native regression passed
- **Observed:** a focused pure-Simple duplication-check binary printed `--help`, then crashed with exit 139.
- **Cause:** the Simple CLI facade calls `rt_cli_exit`, but the core-C runtime only provided the equivalent `rt_exit`; native build accepted an unresolved fallback whose invocation crashed.
- **Fix:** provide `rt_cli_exit` as the core-C ABI alias to `rt_exit`.
- **Regression:** `timeout 20s build/bootstrap/tooling-focused/duplicate-check --help` exited 0 after an incremental rebuild with 65 cached objects; the pre-fix artifact exited 139. `nm -g` reports a defined `rt_cli_exit` symbol.
