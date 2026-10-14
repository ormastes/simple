# MIR JSON C0 escaping and Unicode preservation — 2026-10-12

Status: OPEN; source repair and native fixture AUTHORED_UNEXECUTED. No compiler admission or RSS-fix claim.

Production owner: `src/compiler/50.mir/mir_json.spl:693`, `escape_json_string`; public serializers for string constants, function/local names, block labels and other MIR payloads use it. Original source `f34d789031e37bd38e81e8ce1c109682c075f16b`, file SHA256 `75a5b999fbc4e77e2668755bb6d07553059a8cb702c53b843acff606d85393c2`.

## Defect and evidence

JSON strings must escape all U+0000..U+001F. The original owner handles quote, backslash, LF, CR and TAB but forwards every other unit. Source inspection confirms missing NUL/backspace/form-feed/other C0 branches. Its byte-length/indexed-slice walk also mixes engine-dependent character versus byte slicing; common JSON serializer documents the same Unicode hazard and uses complete `chars()` values.

Old recovery source0e028709 runtime array join uses strlen and can discard NUL and the suffix of its fragment. Target f34 runtime uses registered counted lengths and preserves these bytes. Expected behavior for these sources is source inference. PR3309 records a separate executed older Linux C contract probe showing array join truncation; that authored evidence is not a new candidate/native Windows execution. Truncation can hide invalid escaping. Preserved raw NUL remains invalid JSON. An old compiler producer retains its embedded runtime while emitting a compiler linked with a new runtime; diagnostic Windows snapshot-sink repairs do not qualify join behavior.

## Repair

Keep existing quote/backslash/LF/CR/TAB spellings. Walk `s.chars()` and use `ord()` plus established ASCII hex slices to encode every other C0 unit as six ASCII bytes `\u00XX`. Preserve complete non-ASCII characters, parts accumulation and one join. No exported private helper, runtime symbol, cache relaxation, free/scope reset, or ownership transfer is introduced. GH3309's unrelated prefix-loop optimization is excluded.

Existing `std.common.json.tokenizer` validates raw controls with byte_at and supports four-hex Unicode escapes, BMP chr and surrogate pairs. Native chr(0)/decoder join behavior still requires the counted-runtime qualification. Validating only equality against the old serializer would accept truncated output and is insufficient.

## Acceptance and execution boundary

`test/fixtures/bootstrap/mir_json_c0_escape/main.spl` imports real production serializers and decoder. Its explicit32-entry golden oracle exercises every C0 in isolation and between a/b, plus leading/trailing NUL, adjacent controls, empty/plain strings, quote/backslash, literal \u0000 text, BMP and supplementary Unicode. Both full JSON parser and direct decoder outputs must match original byte length and each byte; input control arrays themselves are validated, preventing broken source escapes from passing. Real MIR local/function names, block label and string constant use the mixed Unicode/control payload; parse checks and exact field-presence checks prevent empty/default outputs. Const string uses canonical pointer-to-I8 text representation.

Native success requires exit0 and exact main.expected stdout. These tests are AUTHORED_UNEXECUTED until a genuine admitted target self-hosted producer can compile and execute them. No Rust seed product-test fallback. Preserve compilation/execution failure evidence, and run this criterion once after the owned repair and qualified producer exist. Ordinary-input golden cases protect existing encoding spellings. This focused fixture does not replace Phase3/generic/formal/HelloWorld or actual backend transport qualification.
