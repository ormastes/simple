# Stage 4 parser rejects detached closing parens after final parameters

- **Status:** FIXED
- **Owner:** `codex-stage4-bootstrap-close`
- **Found:** 2026-08-02, Stage 4 phase 2
- **Area:** pure-Simple composite JIT test runner

Eight adapter calls placed a newline between their final zero-argument lambda
and the closing parenthesis. The staged parser requires that parenthesis on the
same line. The adjacent multiline helper declaration used the same detached
closing form, so it is normalized with the call family.
