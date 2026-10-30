# Lint 08-24 series source dropped by snapshot 4edef8fab8e; specs kept (2026-10-30)

Status: open
Area: compiler/lint (raw_rt_access, raw_sffi_call, lint_checks, fix/rules registry)
Found by: lint spec sweep of test/01_unit/compiler/lint (22 failing files)

## Symptom

| Spec | Failing examples |
|---|---|
| `test/01_unit/compiler/lint/raw_rt_access_spec.spl` | 13 of 41 (after the missing `use` lines were restored) |
| `test/01_unit/compiler/lint/raw_sffi_call_spec.spl` | 1: "shares one lexical snapshot and preserves category ordering" |
| `test/01_unit/compiler/lint/perf_diagnostic_record_spec.spl` | 3: evidence/uncertainty rendering, one-cursor docstring scan, single policy decision |

## Root cause

`4edef8fab8e` ("feat: snapshot current development state", 2026-08-26, 11,225 files) rewound the
2026-08-24 lint performance and RAW-RT series in `src/`. It removed:

- in `35.semantics/lint/raw_rt_access.spl` (-340 lines): `raw_rt_wrapper_binding_is_unshadowed`,
  grouped-callee and parenthesized-import detection, allowlist suffix semantics
- in `lint_checks.spl` and `registry.spl`: `RawSffiCodeSnapshot` / `raw_sffi_code_snapshot`,
  `check_all_rules_with_lines`, `easy_fix_source_view`, the `*_with_view` / `*_snapshot` rule entry
  points, and `lint_source_for_parsed_append` siblings
- `35.semantics/lint/cow_alias_hotpath.spl` (deleted) and parts of `nonexistent_type_lints.spl`

The specs from that series were not rewound. The 2026-09-29 transplant `88aac2ffe28` then carried
those specs onto release/1.0 without the source.

Two small helpers from the series were restored independently
(`lint_rule_code_from_easyfix_id` and `lint_line_may_contain_pass_todo`, PR #5434). The rest is a
multi-file re-land of the series, which is too large for a spec fix.

## Unblock

Re-land the 08-24 series (`a869fa80e67`, `ceac9be66d5`, `c80c4143e9e`, `99215a27c9c` and siblings
on `origin/codex/session-01a02787-rebased-v41`) on top of the current lint tree. Then remove the
`pending` markers that link here.
