# `compiler.common.mission_critical.__init__` is unparseable on the deployed seed

Date: 2026-08-24
Status: OPEN
Severity: medium — the package `__init__` cannot be imported at all, so every
consumer must route around it to the leaf module.

## Symptom

Importing the package rather than a leaf module aborts the compile:

```
[INFO] JIT compilation failed, falling back to interpreter: module load error:
  parse: in ".../src/compiler/00.common/mission_critical/__init__.spl":
  Unexpected token: expected expression, found Dedent
error: compile failed: parse: in ".../src/compiler/00.common/mission_critical/__init__.spl":
  Unexpected token: expected expression, found Dedent
```

## Reproduce

In any `.spl` reachable from a run, replace a leaf import with the package one:

```
use compiler.common.mission_critical.{parse_alloc_allowances}
```

then

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple run scripts/audit/noalloc_manifest_scan.spl
```

Exit status 1 with the parse error above. Switching the import to the leaf
module `compiler.common.mission_critical.alloc_diagnostic_config` makes the
same run exit 0. Measured on the deployed seed
`bin/release/x86_64-unknown-linux-gnu/simple`.

## Suspected cause

`src/compiler/00.common/mission_critical/__init__.spl` uses multi-line
`export use <module>.{ ... }` blocks (lines 1-6 and 9-13) whose continuation
lines are indented; the parser reaches the closing `}` line having consumed a
Dedent it does not expect. The single-line `export ... from <module>` form on
lines 7-8 in the same file does not trip it, which is the discriminator.

## Known workaround sites (both route to the leaf module deliberately)

- `src/compiler/35.semantics/noalloc_checker.spl:47`
- `src/compiler/90.tools/verify/noalloc_manifest_scan.spl` (import block; the
  comment there points at this record)

## Why it matters

The package exists to give `35.semantics` / `80.driver` / `90.tools` one import
surface for the mission-critical contracts. While it is unparseable that
surface does not exist, and each new consumer silently learns to bypass it —
which is how an `__init__` stops being the API and becomes dead text.

## Neighbours worth checking with the same fix

Any other `__init__.spl` using the multi-line `export use X.{...}` form. This
record does not claim to have surveyed them.
