# `check` crashed under interpret mode: dict API on a `[text]` array in expand_check_targets (RESOLVED 2026-09-01)

## Status

RESOLVED — two-line fix in `src/app/check/targets.spl`, no rebuild needed
(src/app is read as source).

## Symptom

`SIMPLE_EXECUTION_MODE=interpret bin/simple.exe check <any file>` exited 1 with

```
error: semantic: type mismatch: cannot convert string to int
```

while the same command WITHOUT that env var passed. Impact multiplier: the test
runner exports `SIMPLE_EXECUTION_MODE=interpret` +
`SIMPLE_RUNTIME_MODE=interpreter` (`src/app/test_runner_new/test_runner_single.spl:1088-1089`)
into spec processes, and a spec-spawned `check` child inherits them — so
`check` failed inside EVERY spec that shells out to it, while looking healthy
from an interactive shell. This surfaced immediately after the stale-seed
decorator failure was fixed
(`check_broken_on_windows_stale_seed_decorator_2026-09-01.md`): the new
contract spec `check_clean_file_passes_spec.spl` went red with child
`code=1 outlen=0`, and the evidence print localised it.

## Root cause (file:line)

`src/app/check/targets.spl` `expand_check_targets`:

```
var seen_targets: [text] = []      # line 10 — an ARRAY
...
seen_targets[target_identity] = true          # line 16: string-indexed bool store
if not seen_files.contains_key(target_identity):  # line 18: dict API on [text]
```

Dict bookkeeping written against arrays. The hybrid JIT engine tolerated it;
the pure interpreter lowers `array[string_key] = v` through `Value::as_int()`
on the index (`src/compiler_rust/compiler/src/value_impl.rs:117`), which is a
hard semantic error for `Str`. Bisection: imports clean, `check_option_error` /
`parse_log_options` clean, first faulting call `expand_check_targets`.

## Fix

Line 16 → `seen_targets.push(target_identity)`; line 18 → `.contains(...)`.
Matches the surrounding code's own idiom (`seen_targets.contains(...)` on line
14, `seen_files.push(...)` on line 19). No behaviour change intended or
observed on the hybrid path.

## Evidence (seed md5 f9bf124d933a0de0af5d999444234996)

| command | before | after |
|---|---|---|
| `check hello.spl` (hybrid) | rc=0 | rc=0 |
| `SIMPLE_EXECUTION_MODE=interpret check hello.spl` | rc=1 `cannot convert string to int` | rc=0 `All checks passed` |
| `test check_clean_file_passes_spec.spl` | FAIL (child code=1) | PASS |
| `test check_broken_file_reports_error_spec.spl` | — | PASS |

## Specs (per the two-spec rule)

- Reproducing + generalization:
  `test/01_unit/app/check/expand_check_targets_dedupe_no_dict_api_spec.spl`
  (verified RED against the pre-fix file: 2/2 examples fail with the exact error; runs under the runner interpret mode and drives both mixed-API sites via a
  duplicate-target and a distinct-target expansion).
- End-to-end contract (the spec that caught it):
  `test/01_unit/app/cli/check_clean_file_passes_spec.spl` and
  `test/01_unit/app/cli/check_broken_file_reports_error_spec.spl`.

## Cross-platform

Pure `.spl` fix, platform-agnostic; nothing Unix-side touched. The latent
question — why the hybrid engine ACCEPTS `array[string] = bool` silently — is
an engine-divergence issue worth its own look; this record fixes the caller,
not the divergence.
