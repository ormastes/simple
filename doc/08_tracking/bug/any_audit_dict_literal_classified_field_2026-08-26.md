# any_audit: dict-literal type value position classified `field` instead of `generic` (pre-existing)
**Status:** OPEN (unverified 2026-09-12)

- Date: 2026-08-26
- Spec: `test/01_unit/app/any_audit/any_audit_classify_spec.spl`
- Failing example: `classifies a dict-literal type value position as generic`
  (`expected [field] to equal [generic]`)
- Pre-existing at HEAD `e656b0ecb98`: the UNMODIFIED source (extracted via
  `git show HEAD:<spec>`, run as a sibling file) fails identically —
  `Results: 22 total, 21 passed, 1 failed`. Not caused by the sspec
  modernization edits (comments/`step()` only).
- Unblock condition: fix the classifier in `src/app/any_audit/` so a
  dict-literal `{K: V}` type in value position classifies as `generic`,
  then this spec goes green.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and has no cheap repro reachable within budget; left open with an explicit unverified status line.
