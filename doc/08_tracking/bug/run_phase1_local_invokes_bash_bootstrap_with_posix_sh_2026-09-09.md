# `run-phase1-local` invokes a Bash bootstrap with POSIX `sh`

**Date:** 2026-09-09  
**Status:** Fixed in the physical paged-KV activation lane

## Symptom

On Linux, the canonical local Stage-2 bootstrap entrypoint exited immediately:

```text
scripts/bootstrap/bootstrap-windows.sh: 2: set: Illegal option -o pipefail
```

## Cause

`scripts/bootstrap/run-phase1-local.shs` invoked
`bootstrap-windows.sh` through `sh`, overriding that script's Bash shebang.
The target uses Bash arrays, `BASH_SOURCE`, and `set -o pipefail`.

## Resolution

The wrapper now invokes the target explicitly with `bash`. This preserves the
existing bootstrap arguments and lets the Bash-owned entrypoint reach the
canonical `bootstrap-from-scratch.sh` pipeline.
