# MCP SDK JSON encoding once

Executable source: `test/01_unit/lib/mcp_sdk/json_encoding_once_spec.spl`.

Status: authored manual. The two SSpec scenarios and docgen are **NOT_RUN** in this completion lane. This manual describes assertions in the landed source; it is not an execution receipt.

## Scenario 1: text survives one strict JSON decode

1. **Prepare the real fixture.** Construct six samples: empty text; quotes and backslashes; newline, carriage return and tab; Korean, accented text and emoji; all control characters U+0000–U+001F; and Korean/quote/NUL/emoji mixed text. Controls and NUL are constructed with `char_from_code`.
2. **Invoke the production owner.** Pass each sample to SDK `js`, `make_tool_result`, and `make_tool_error`. Parse each returned wire value once with `json_parse_value_strict`.
3. **Check the observed contract.** Assert successful strict parsing and exact decoded text equality. Tool responses must contain exactly one content item, whose `text` equals the original sample. An extra escaping layer or an unescaped JSON control violates these assertions.

## Scenario 2: structured schema and error data remain objects

1. **Prepare the real fixture.** Supply an object schema, a quoted tool description, a quoted error message, and an object containing `device: "COM7"`.
2. **Invoke the production owner.** Serialize through `tool_def_to_json` and `jsonrpc_error_with_data`, then strictly decode each response once.
3. **Check the observed contract.** Assert exact description and message text, and access `inputSchema.type` and `error.data.device` as object fields. These neighboring controls reject accidentally quoting structured JSON along with text fields.

## Evidence boundaries

The separate native fixture `test/fixtures/mcp/sdk_json_once/main.spl` emits fourteen actual SDK builder cases for seven samples: 98 records. PR #7501 and its bug note report historical strict single-decode success for image SHA256 `eca1ea585499beae85d2b6de1b450a2425f34881e247a3478375303a7b446ee2`, with receipt `build/review/serial-mcp-native-provider-cc13-attempt3/sdk-roundtrip/qualification.sdn`. That receipt and its records were not locally available for independent verification in this lane. The historical report is not a current-source SSpec PASS.

Neither this unit spec nor that serialization fixture exercises a real MCP stdin/stdout session. Current-source MCP stdio qualification, mandatory compiler/lib/MCP/LSP checks, applicable native smoke, and docgen remain **NOT_RUN** here. No startup latency, hardware/provider qualification, or broader text-runtime correctness is established by these controls.
