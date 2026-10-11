# UI test API JSON field extraction

Source: `test/01_unit/app/ui/test_api_json_spec.spl`.
Owner: `src/app/ui.test_api/json.spl`.
Requirement: REQ-SSPEC-SYSTEM.

Status: **Phase1 seed diagnostics PASS, 8/8**. Native acceptance and SPipe
docgen remain unrun. The 80% annotation is a target, not measured coverage.
Producer and exact source identities are retained in
`build/phase-one-ui-diagnostic/json-repair-inputs.json`; execution log:
`build/phase-one-ui-diagnostic/test_api_json_spec/cycle-one.log`.
This manual is synchronized with the source below.

## Manual flow

1. Read `event_type:"key"` followed by `key:"Enter"`; require both actual
   member values and the same behavior with reversed order.
2. Read a top-level key after nested-object and array decoys; nested-only names
   must not satisfy a top-level lookup.
3. Decode escaped quotes, backslashes and newlines while ignoring field-like
   text embedded inside string values.
4. Decode an escaped member name and Unicode value.
5. Accept space, tab, carriage return and newline around JSON members.
6. Return the existing empty-string sentinel for absent, empty or non-string
   members, including numbers, booleans, null, objects and arrays.
7. Return empty for malformed documents or non-object roots.
8. Preserve the shared parser's documented last-value-wins duplicate-key policy.

The public function reuses the typed shared JSON parser and reads only a
top-level string member. Request handlers retain their existing missing-field
responses when this text-only helper returns empty.

Bug and retained pre-fix system evidence:
`doc/08_tracking/bug/ui_test_api_json_key_value_collision_2026-10-11.md`.
The unchanged named-key request remains covered by handler integration in
`test/03_system/gui/ui/web_test_api_spec.spl`.

<details>
<summary>Executable SSpec</summary>

```simple
# UI test API JSON field extraction regression.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/app/ui.test_api/json.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# bug: doc/08_tracking/bug/ui_test_api_json_key_value_collision_2026-10-11.md

use std.spec.{describe, it, expect, step}
use app.ui.test_api.json.{extract_json_field}

describe "UI test API top-level JSON string fields":
    it "should find a key after an earlier string value with the same spelling":
        step("Read the valid named-key event payload")
        val body = "{\"event_type\":\"key\",\"key\":\"Enter\"}"
        expect(extract_json_field(body, "event_type")).to_equal("key")
        expect(extract_json_field(body, "key")).to_equal("Enter")
        expect(extract_json_field("{\"key\":\"Escape\",\"event_type\":\"key\"}", "key")).to_equal("Escape")

    it "should ignore matching member names inside nested objects and arrays":
        step("Read the top-level key past nested decoys")
        val body = "{\"metadata\":{\"key\":\"nested\"},\"items\":[{\"key\":\"array\"}],\"key\":\"Enter\"}"
        expect(extract_json_field(body, "key")).to_equal("Enter")
        expect(extract_json_field("{\"metadata\":{\"key\":\"nested\"}}", "key")).to_equal("")

    it "should decode escaped string content without treating it as a field":
        step("Decode quotes backslashes and line breaks in a string value")
        val body = "{\"text\":\"say \\\"hi\\\" \\\\ path\\nnext\",\"key\":\"Enter\"}"
        expect(extract_json_field(body, "text")).to_equal("say \"hi\" \\ path\nnext")
        expect(extract_json_field(body, "key")).to_equal("Enter")
        expect(extract_json_field("{\"text\":\"\\\"key\\\":\\\"decoy\\\"\",\"key\":\"Escape\"}", "key")).to_equal("Escape")

    it "should decode escaped member names and Unicode values":
        step("Read a decoded JSON member name")
        expect(extract_json_field("{\"k\\u0065y\":\"\\u0045nter\"}", "key")).to_equal("Enter")

    it "should accept JSON whitespace around members":
        step("Read a field surrounded by JSON whitespace")
        expect(extract_json_field("{\n\t\"key\"\r : \t\"Enter\"\n}", "key")).to_equal("Enter")

    it "should return empty for absent empty and non-string values":
        step("Read absent or non-string members through the text-only API")
        expect(extract_json_field("{}", "key")).to_equal("")
        expect(extract_json_field("{\"key\":\"\"}", "key")).to_equal("")
        expect(extract_json_field("{\"key\":42}", "key")).to_equal("")
        expect(extract_json_field("{\"key\":true}", "key")).to_equal("")
        expect(extract_json_field("{\"key\":null}", "key")).to_equal("")
        expect(extract_json_field("{\"key\":{\"value\":\"Enter\"}}", "key")).to_equal("")
        expect(extract_json_field("{\"key\":[\"Enter\"]}", "key")).to_equal("")

    it "should reject malformed JSON and non-object roots":
        step("Reject incomplete trailing and non-object payloads")
        expect(extract_json_field("", "key")).to_equal("")
        expect(extract_json_field("{\"key\":\"Enter", "key")).to_equal("")
        expect(extract_json_field("{\"key\":\"Enter\"} trailing", "key")).to_equal("")
        expect(extract_json_field("{\"key\":\"Enter\",}", "key")).to_equal("")
        expect(extract_json_field("[{\"key\":\"Enter\"}]", "key")).to_equal("")
        expect(extract_json_field("\"key\"", "key")).to_equal("")

    it "should retain the shared parser last-value-wins policy":
        step("Read the final top-level value for a duplicate name")
        expect(extract_json_field("{\"key\":\"Escape\",\"key\":\"Enter\"}", "key")).to_equal("Enter")
```

</details>
