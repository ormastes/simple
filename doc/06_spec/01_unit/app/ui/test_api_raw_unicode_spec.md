# UI test API raw Unicode JSON regression

Source: `test/01_unit/app/ui/test_api_raw_unicode_spec.spl`.
Owner: `src/app/ui.test_api/json.spl`.
Requirement: REQ-SSPEC-SYSTEM.

Status: **Phase1 seed diagnostic PASS: four executed scenarios, four passed**.
Evidence: `build/phase-one-ui-diagnostic/test_api_raw_unicode_spec/cycle-one.log`.
This is diagnostic evidence, not native acceptance or docgen validation.
The 80% annotation is an admission target, not measured coverage. SPipe docgen
validation is pending; this manual mirrors the source.

## Manual flow

1. Read raw Korean text followed by whitespace and another JSON member.
   Require the exact Korean text and the later key.
2. Read a Korean member name. Require its exact Korean value, successful lookup
   of the subsequent ASCII key, and empty output for an absent Korean name.
3. Read emoji mixed with Korean text and spaces. Require preservation of both
   emoji and all leading/trailing spaces inside the value, and find the later key.
4. Read past nested objects and arrays containing raw Unicode strings.
   Require the top-level key and prevent nested member names from leaking into
   top-level lookup.

All observations call the production `extract_json_field` function; the
fixtures retain their original Unicode text. These tests cover JSON extraction
only. They do not claim correctness of the HTTP typing handler's per-character
event dispatch, which is a separate source-review finding.

<details>
<summary>Executable SSpec</summary>

```simple
# Raw Unicode JSON strings must preserve character boundaries around whitespace.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/app/ui.test_api/json.spl 80%
# Coverage percentage is an admission target, not measured coverage.

use std.spec.{describe, it, expect, step}
use app.ui.test_api.json.{extract_json_field}

describe "UI test API raw Unicode JSON fields":
    it "should preserve Korean text before whitespace and a later field":
        step("Read Korean text followed by spaced JSON syntax")
        val body = "{\"label\":\"한글\", \n\t\"key\" : \"Enter\"}"
        expect(extract_json_field(body, "label")).to_equal("한글")
        expect(extract_json_field(body, "key")).to_equal("Enter")

    it "should resolve a raw Unicode member name without losing its value":
        step("Read a Korean member name and Korean value")
        val body = "{\"이름\" : \"윤\", \"key\":\"Escape\"}"
        expect(extract_json_field(body, "이름")).to_equal("윤")
        expect(extract_json_field(body, "key")).to_equal("Escape")
        expect(extract_json_field(body, "없는이름")).to_equal("")

    it "should preserve emoji and surrounding spaces inside string values":
        step("Read emoji and spaces before a later string member")
        val body = "{\"text\":\" 😀 안녕 😀 \",  \"key\" : \"Space\"}"
        expect(extract_json_field(body, "text")).to_equal(" 😀 안녕 😀 ")
        expect(extract_json_field(body, "key")).to_equal("Space")

    it "should ignore nested raw Unicode values before the requested top-level field":
        step("Read a top-level key after nested Unicode object and array values")
        val body = "{\"metadata\":{\"이름\":\"한글\",\"key\":\"중첩\"}, \"items\":[\"😀\", \"서울\"], \"key\":\"Tab\"}"
        expect(extract_json_field(body, "key")).to_equal("Tab")
        expect(extract_json_field(body, "이름")).to_equal("")
```

</details>
