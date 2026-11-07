# MCP SDK text fields must be encoded exactly once

Status: focused native evidence passed; full pure-runtime gates pending.

Fifteen SDK text fields preescaped strings before js encoded them again, so one JSON decode returned extra escapes. The SDK escape_json helper also omitted several JSON control characters. Six production files remove those preescapes and delegate the stable helper API to the existing common text encoder. Structured schemas, arguments and error data remain raw JSON.

The authored native fixture exercised fourteen actual SDK builders with seven samples, including all 32 controls and mixed Korean/quote/NUL/emoji text. The strict single-decode oracle passed all 98 records using native image eca1ea585499beae85d2b6de1b450a2425f34881e247a3478375303a7b446ee2. Evidence: build/review/serial-mcp-native-provider-cc13-attempt3/sdk-roundtrip/qualification.sdn. The original serial strict JSON failure was retained and the corrected consumer passed its strict protocol campaign; this note does not incorporate or qualify the separate four-C-source provider changes.

The unit SSpec and mandatory full pure compiler/lib/MCP/LSP checks and MCP stdio integration remain pending. Focused native evidence does not qualify hardware, SSH/proxy transport or deployment. No native binary is distributed by this source change.
