# SDN parser: non-ASCII comment corrupts keys; JSON-form input keeps key quotes

- Found: 2026-11-12, lane U1 (DiagnosticRulePolicy), seed `bin/simple.exe` (interpreter).
- Component: `src/lib/common/sdn/parser.spl` (`parse`).
- Status: open

## Repro 1 — non-ASCII byte before the document shifts every key
A file whose leading `#` comment contains `§` (U+00A7) or `—` (U+2014), then
`diagnostic_policy:\n    version: 1\n    rules: ...`, parses to a ROOT dict with
keys `ostic_policy`, `ersion`, `ules` — truncated by the multibyte overhang and
flattened to one level. Same file with ASCII-only comments parses correctly.
Likely a byte-offset vs char-index mix in the line/indent scanner.
Workaround (tagged): `config/policy/diagnostic_policy.sdn` is kept ASCII-only.

## Repro 2 — JSON-form document keeps quotes in keys
`parse("{\"code\":\"E1\"}")` yields a dict whose key is `"code"` (with the
quote characters), so `.get("code")` is None. Workaround: the DiagnosticV1
JSON round-trip spec uses `std.common.json.parser.json_parse`.

## Expected
Both inputs yield keys without offset damage or quote characters. Add a
repro spec under `test/01_unit/lib/common/sdn/` when fixing.
