# Current-producer frontend helper source workarounds

Parent bug: phase2_subsystem_helper_mir_failures_2026-10-05.
Status: source workarounds authored; native validation UNRUN.

The six-products-current-proven-transport1/helper-build-failures.json packet
records all12 generator/main-verdict helper compile steps failed before test
enumeration. Frontend diagnostics include undefined FlatPoolReader, unresolved
new/reject_malformed in flat_pool_codec, and unresolved ord in placeholder_lambda.
Other lexer and shared I/O/Result/enum failures remain independently open.

new_canonical called its sibling FlatPoolReader.new factory through a class
receiver that the current native producer failed to resolve. It now directly
constructs an explicitly typed cursor with the identical field initialization,
canonical enabled, and the existing malformed-frame rejection. No decode gate,
budget, cursor state or ownership policy is removed. This is a source workaround;
general sibling factory/method resolution is not claimed repaired.

parse_placeholder_number already validates every character as an ASCII decimal
digit. byte_at(i) therefore gives exactly the prior intended ord code, with no
one-character slice allocation. Invalid/non-ASCII names still return -1 before
conversion. Overflow behavior is unchanged. The text.ord lowering gap remains
open for general text callers, where byte access would not preserve semantics.

The native_helper_frontend_owner smoke covers positive canonical decoding,
missing-final-newline rejection/details, distinct cursor ownership, multi-digit
conversion and invalid names. Existing canonical frame specs remain applicable.
Next validation uses the current P2 producer in a fresh owned overlay with caches
preserved; no compiler rebuild or previous capped numeric-payload retry is part
of this patch. No runtime correctness/RSS/timing PASS is claimed. Static cost is
unchanged for cursor construction and lower for ASCII conversion (no slice).

## Additional ASCII/conversion group

effect_parse_budget and asm target-version parse_int_text also used text.ord.
Both grammars are ASCII decimal, now checked with byte codes48..57. The effect
budget rejects any nondigit; the existing ASM helper deliberately skips nondigits,
and that distinction remains tested. Neither change changes general Unicode ord.
CLI integer defaults now call the existing string_to_int owner explicitly rather
than unresolved text.to_int dispatch; default token text and AST type are retained.
native_helper_frontend_ascii exercises those three real owner entry points,
including invalid Unicode digits and the parsed CLI integer AST payload.
Execution remains UNRUN; CoreLexer and HashMap receiver work is a separate lane.
