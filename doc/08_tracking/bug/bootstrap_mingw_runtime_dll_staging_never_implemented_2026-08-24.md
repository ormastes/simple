# check-bootstrap-portability's MinGW runtime-DLL assertion has never been satisfiable

**Date:** 2026-08-24
**Status:** OPEN — genuine unimplemented feature, NOT drift and NOT a false red
**Scope:** Windows/MinGW cross lane only; does not affect Linux/macOS/SimpleOS bootstraps

## Symptom

`sh scripts/check/check-bootstrap-portability.shs` ends:

```
FAIL: MinGW runtime DLL is not staged
```

The assertion (`scripts/check/check-bootstrap-portability.shs:224-225`) is a
source-static grep on the bootstrap driver:

```sh
grep -Fq '"${rust_authority_profile_dir}/simple_runtime.dll"' \
  scripts/bootstrap/bootstrap-from-scratch.sh ||
  fail "MinGW runtime DLL is not staged"
```

## Finding

`scripts/bootstrap/bootstrap-from-scratch.sh` contains **zero** occurrences of
`.dll` — not the literal above, not any other spelling. The driver stages
`simple`, `libsimple_native_all.a`, `libsimple_compiler_backfill.a` and
`deps/libsimple_runtime.a`; there is no DLL staging path at all.
`rust_authority_profile_dir` itself is used at only two sites (`:5377` defining
it, `:5649` passing it), neither of which mentions a DLL.

## This is not the rename/move-drift class

Two other reds found in the same sweep on the same day WERE drift (a gate
grepping a path that had become a re-export facade; a fixture missing a tuple
member the publisher derives). This one is not, and the difference was
established by checking history rather than assumed:

| revision | `simple_runtime.dll` in driver |
|---|---|
| `6f86ff32a7d~1` (before the fourth tree wipe) | 0 |
| `6f86ff32a7d` (the wipe) | 0 |
| `ae55a746719` (the restore) | 0 |
| `9a0cfd1e5d6` | 0 |
| `origin/main` | 0 |

An initial hypothesis that the staging had been lost in the fourth tree wipe and
only partially restored is therefore **refuted**: it was never there. The gate
asserts a capability that was specified and never implemented, so it has been
RED since the day it was written.

## Deliberately not "fixed"

The gate is correct to fail and must NOT be relaxed, repointed, or deleted to
make a board green — that would convert a real missing feature into a fake pass,
which is the exact defect class this repo keeps finding. The work is to
implement MinGW runtime-DLL staging in the driver (stage
`simple_runtime.dll` out of `rust_authority_profile_dir` alongside the existing
static members, under the same immutable-publication tuple discipline used by
`bootstrap_stage3_publish_seed_generation`).

Out of scope for the current Linux/arm/riscv/x86 bootstrap goal; recorded so it
is not mistaken for drift by the next sweep.
