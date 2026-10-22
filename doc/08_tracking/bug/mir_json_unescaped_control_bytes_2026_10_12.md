# MIR JSON escape function does not escape all control bytes

Status: OPEN, source-confirmed; no repair in the runtime join change.

`src/compiler/50.mir/mir_json.spl::escape_json_string` handles quote, backslash,
LF, CR and TAB. Other JSON control bytes, including NUL, enter the ordinary-byte
fragment path. A counted fragment join retains literal NUL, which is not valid
JSON string encoding; the old native `rt_array_join_any` instead drops NUL through
strlen. Neither behavior establishes the required escaped `\u0000` representation.

This defect precedes the proposed outer function/block fragment-join change in
PR3198. Do not label NUL loss a newly introduced serializer regression solely
because that proposal adds a join. A focused repair must escape all remaining
U+0000..U+001F characters, preserve UTF-8 and existing escapes, and execute the
actual serializer plus a JSON decoder with independent golden byte assertions.
Native serializer execution is currently blocked by its existing MIR dependency
lowering failures. No source repair or end-to-end parity is claimed here.
