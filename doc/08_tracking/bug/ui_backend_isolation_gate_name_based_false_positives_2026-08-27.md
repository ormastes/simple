# `check-ui-backend-isolation.shs` flags in-repo Simple functions whose NAME starts with `rt_` (2026-08-27)

**Status:** OPEN. Found while clearing the gate's RED on `origin/main`.

## Symptom

The gate reports `src/app/io/env_access_host.spl` and `src/app/io/rt_hal_isolated_host.spl` as
backend-isolation violations. Neither file contains a single backend extern:

```
$ grep -c 'extern fn rt_' src/app/io/env_access_host.spl        # 0
$ grep -c 'extern fn rt_' src/app/io/rt_hal_isolated_host.spl   # 0
```

Every flagged line is either a `pub fn rt_hal_*` **definition** written in Simple, or a call to
that same in-repo Simple function. The gate's name-based pattern (`rt_[a-z0-9_]+\s*\(`) matches on
the identifier's spelling alone, so any Simple function named `rt_*` trips it with no backend
primitive involved. This is a false positive, not shielded debt.

## Why it matters more than a cosmetic miscount

These two entries were absorbed into `ui_backend_isolation_baseline.txt` to clear the gate. A
baseline entry is a written statement that a file carries accepted debt — for these two that
statement is **false**, and it will stay false and unexamined until someone re-derives it. A gate
that mislabels clean files trains readers to treat its output as noise, which is how the real
violations in the same list stop being read.

## Not fixed here, deliberately

The obvious fix — rename the `rt_hal_*` family — was rejected as non-minimal: it would have to
cover every `rt_hal_*` symbol across the file and its callers to actually clear the pattern, and
`env_access_host.spl` is the file whose unbalanced-paren incident made `main` un-test-runnable on
2026-08-25 (`origin_main_not_test_runnable_env_access_host_parse_2026-08-25.md`). Churning it to
satisfy a regex is the wrong trade.

## Suggested fix

Narrow the gate to what it actually means to catch: a call is only a backend-isolation violation
if the symbol is **declared** `extern` (in the file, or in a module it imports). Resolving against
declarations rather than spelling removes this whole false-positive class and costs no detection
power — a real backend primitive is always an extern somewhere. Until then, the two entries above
should be removed from the baseline in the same change that narrows the pattern, not before.
