# Total text integer conversion loses scalar proof before nil coalescing

Status: source root-fix passes focused MIR regression; native fixed-compiler/P3 qualification pending.

Actual native closure counter attempt04 accepted genuine inherited SCV pins
but rejected the valid generation3/count16144 inventory as
`inventory-count-invalid`. Independent byte inspection found6,101,705 bytes,
16,147 newline-separated rows, no trailing newline: header count+3 is exact.

The actual C39 aggregate object
`build/verify/p3-native-closure-counter-object-20261026-04/counter.o`
contains `lib.scv.compile_source_inventory.compile_source_inventory_decode_content_v1`:
-0x8d70 calls `rt_string_to_int_lenient` for the generation substring.
-0x8d78 passes that raw result to `rt_is_some`.
-0x8d8c assigns-1 when that predicate is false.
The exact linked retained `runtime_native.o` implements `rt_is_some` at0x10220
with `cmp x0,#3`; it returnsfalse for that nil sentinel. Its lenient parse
at0x51a0 branches to `rt_string_to_int`; the strtoll return at0x168a8 reaches
the return epilogue unchanged. Legitimate raw integer3 therefore becomes nil.
The count parser has the same call pattern at0x8dfc/0x8e04. These are actual
object relocations/instructions, not conclusions from symbol names alone.

`to_int`/`to_i64` are total scalar conversions, unlike strict optional
`parse_int`. Their existing raw-runtime mapping must stay. The pure-SPL text
builtin lowering records plain Int64 metadata for find/index/rfind results but
omits it for these total conversions. Existing NullCoalesce lowering already
returns a proven non-optional scalar without a presence test or evaluation of
the default; the root fix carries the same Int64 proof for the selected total
text conversions. It does not alter runtime APIs, custom-owner dispatch,
optional parse_int semantics, Error/Infer type recovery or general externs.

Focused regression plan executes the real parser->HIR->MIR pipeline: total
sentinel3, to_int twin and actual inventory-style substring chain must emit the
raw conversion and omit rt_is_some/default effects; genuine strict-parser and
opaque-extern controls must retain their presence/default branches. This
checks the changed lowering, rather than relying on the seed interpreter's
already-correct text evaluation.

Native acceptance proposal after a newly qualified compiler exists: compile a
small real source fixture covering total values0/1/3/7/8/16144, a default with
an observable counter, strict parse_int success/failure, then execute actual
canonical SCV decoder content. The retained P2 cannot acquire a source-only
lowering fix without rebuilding, so no current native PASS may be inferred.
The separate validated decimal decoder workaround can be compiled/relinked
through real current APIs while preserving canonical roundtrip checks; it is
not a substitute for fixing compiler scalar proof propagation.

No P2/Rust/runtime rebuild or original failed-receipt mutation is authorized
by this root fix. The earlier cold git-event-refresh failure has other nil
return sites and is not claimed solved merely by diagnosing inherited decode.

Validation2026-10-26: the exact five-case parser->HIR->MIR regression passed
5/5, no skips/drops/failures, under the retained-gen13 interpreter and canonical
guard. Receipt completeexit0, quiescent1, enforced3145728KiB cap,
peak1320016KiB, observererrors0, measurementbudgetcomplete1; exact source,
spec, seed and runtime before/after hashes matched. Evidence:
review workspace `build/verify/text-total-parse-scalar-proof-regression-20261026-01/`.
Astra reviewed the exact owner and final source/result. Error/Infer recovery
was not broadened. Existing unrelated LFS checkout changes are excluded.
These tests execute the changed pure-SPL lowering; no rebuilt native compiler
or whole P3 qualification is claimed.
