# API Predicate Prefix Migration Plan

Date: 2026-05-13

## Scope

The production naming contract prefers predicate-form APIs for new public
surfaces, but the current codebase still has established `is_` and `has_`
helpers. This plan freezes that debt and defines how to reduce it without
breaking callers.

## Current Baseline

`bin/simple run scripts/audit/api_consistency_audit.spl --mode=interpreter` reports:

| Scope | Advisory `is_`/`has_` declarations |
| --- | ---: |
| `src/app` | 204 |
| `src/compiler` | 600 |
| `src/lib/common` | 623 |
| Total | 1427 |

The baseline is stored in `scripts/audit/api_consistency_baseline.json`.
Increasing the total or any scoped count fails the audit.

## Migration Rules

1. New public-ish APIs use predicate form or a short noun/verb form instead of
   `is_` or `has_`.
2. Existing `is_`/`has_` APIs stay source-compatible until a caller migration
   exists.
3. For each migrated predicate, add the preferred API first, keep the old name
   as a forwarding alias, and document the canonical spelling.
4. Reduce the baseline only after callers are migrated and tests cover the
   canonical name.
5. Do not lower the baseline in the same change that introduces unrelated API
   churn.

## Verification

Run:

```sh
python3 -m json.tool scripts/audit/api_consistency_baseline.json >/dev/null
bin/simple check scripts/audit/api_consistency_audit.spl --mode=interpreter
bin/simple run scripts/audit/api_consistency_audit.spl --mode=interpreter
```

Passing evidence means there are no hard-rejected API names and no new
predicate-prefix debt beyond the checked baseline.
