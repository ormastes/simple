# `lint --warn-all --deny-all` ignored allowed style diagnostics

- **Status:** FIXED in source; current Stage 4 qualification remains pending.
- **Reproducer:** an ST001 function name such as `CamelCase` exited `0` because `style_convention` defaulted to `Warn`, while applying configured `Warn` preserved the diagnostic's built-in `Allow` level.
- **Root fix:** keep style diagnostics suppressed by default (`style_convention = allow`), then promote an original `Allow` diagnostic when configuration or `--warn-all` selects `Warn`. Existing `Deny` diagnostics are never downgraded.
- **Regression:** `lint_profile_spec.spl` proves baseline ST001 exits `0`, `--warn-all --deny-all` exits `1`, and a clean source exits `0`, using a PID/time-unique fixture.
- **Related open case:** STUB002 is also declared `Allow` but shares the `stub_impl` config name with deny-level STUB001/STUB003; per-code mapping is required before claiming every built-in Allow diagnostic has independent policy.
