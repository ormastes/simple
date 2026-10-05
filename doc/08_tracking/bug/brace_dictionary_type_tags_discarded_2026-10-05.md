# Brace dictionary annotation drops key/value type tags

Status: FIX AUTHORED, native validation pending. This repairs the parser defect
underlying native_dictionary_array_value_erasure_2026-10-05.md; the existing
typed-local source workaround remains independent.

`parser_parse_type_impl` parsed `{K: V}` children, discarded both returned
tags, and returned bare TYPE_DICT. The flat AST bridge maps that sentinel to
an argumentless Dict; HIR lowers it as Dict<Any,Any>. Index lowering already
propagates typed dictionary values correctly, but receives Any here. The
trait lifecycle fixture consequently failed both native backends on a direct
indexed `.contains` and two direct indexed for-in loops. No fixture executed.

Fix: register both tags in the existing dict_type_register table, exactly as
Dict<K,V> does, then preserve the existing optional suffix handling. Nested
arrays, dictionaries, and generic tags remain owned by their existing
registries. Empty/untyped brace behavior and malformed syntax recovery are
unchanged. No field representation, runtime ownership, or MIR ABI changes.
Inline union child grammar is not expanded: this branch continues to use
parser_parse_type, just as before. Union parsing/representation is untouched.

Tests: dictionary_brace_type_identity_spec.spl checks parsed structural types;
native_dictionary_array_direct.spl exercises direct method calls and loops,
class fields, empty values, guarded missing keys, nested arrays/dictionaries.
All execution is UNRUN until a corrected producer can run these tests.

Memory/performance review: adds one existing intern-table probe per explicit
brace annotation. Repeated key/value pairs reuse the same registry entry;
new distinct pairs retain two i64 tags, bounded by the existing dictionary
tag range and diagnosed on exhaustion. This matches generic Dict syntax and
avoids new per-expression allocations/scans. Measured RSS and elapsed-time
regressions remain UNRUN; compare parser-heavy repeated/distinct annotation
fixtures and the direct native repro under both backends after bootstrap
finishes. No sub-0.1s compile performance claim is made.
