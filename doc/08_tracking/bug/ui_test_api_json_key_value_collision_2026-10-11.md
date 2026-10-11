# UI test API confuses a JSON string value with a member name

Date: 2026-10-11.
Status: source fix verified by Phase1 seed diagnostics; native acceptance
unverified.

## Retained failure evidence

Run log:
`build/phase-one-ui-diagnostic/web_test_api_spec/cycle-one.log`.
Exact invocation:
`build/phase-one-ui-diagnostic/web_test_api_spec/command.json`.

The admitted Phase1 diagnostic executed seven web API scenarios: six passed and
one failed. The failing scenario was
`should dispatch a named key through the event endpoint`. Its final diagnostic
was `semantic: array index out of bounds: index is 0 but length is 0` because
the event callback received no event. This is seed diagnostic evidence, not
self-hosted/native release acceptance.

The valid request body was
`{"event_type":"key","key":"Enter"}`, sent to POST `/api/test/event`.

## Production cause

`src/app/ui.test_api/json.spl::extract_json_field` searched for the first textual
occurrence of `"key"`. That occurrence is the string value of `event_type`,
followed by a comma rather than a colon. The helper therefore returned empty
without reaching the actual member name. The handler treated the key as absent,
returned a missing-field response, and injected no event. The later unguarded
array access obscured the failed response/count assertions in the report.

The same scanner could select nested names and stopped at escaped quotes.
Changing request member order would conceal the valid-input defect.

## Prepared repair and regression scope

Replace the substring scanner with the existing typed `common.json.value`
parser, top-level lookup, and string extraction. Missing/non-string members,
malformed documents and non-object roots retain the empty-string return contract.
String escapes are decoded by the shared tokenizer; duplicate keys use its
documented last-value-wins policy.

New regression:
`test/01_unit/app/ui/test_api_json_spec.spl`, with its matching manual at
`doc/06_spec/01_unit/app/ui/test_api_json_spec.md`.
Eight scenarios cover value/name collisions, reordered keys, nested decoys,
escaped member names and values, JSON whitespace, empty/non-string results,
malformed/non-object inputs, and duplicate keys.

The original system request body remains unchanged. Array access in its failed
named-key scenario is guarded so response and event-count failures remain visible.

## Verification

The admitted Linux Phase1 seed at SHA256
`0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`
executed the focused unit regression: **8/8 PASS**, and the affected handler
integration: **7/7 PASS**, preserving the original request body. Both resource
guards exited zero with `quiescent=1`. Logs:
`build/phase-one-ui-diagnostic/test_api_json_spec/cycle-one.log` and
`build/phase-one-ui-diagnostic/web_test_api_spec/cycle-two.log`.
Commands, source hashes, and producer identity are retained alongside them and
in `build/phase-one-ui-diagnostic/json-repair-inputs.json`.

This is focused seed evidence, not native acceptance, measured coverage, or
whole-suite success. Docgen, full protocol transport, and browser acceptance
remain unverified. Each extraction now parses the complete document; no
performance improvement is claimed.
