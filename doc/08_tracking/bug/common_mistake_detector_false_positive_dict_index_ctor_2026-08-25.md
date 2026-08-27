# "Common mistake" detector misreads `dict[Ctor(...)] = v` as `List[T]` generics (2026-08-25)

**Status:** FIXED 2026-08-25 (see Resolution).

**Correction to the first version of this record:** it claimed the hint "blocks `bin/simple test`".
It does not. `WrongBrackets` is classified `ErrorHintLevel::Warning` (`error_recovery.rs`) and both
renderers honour the level, so it is NOISE, not a fatal error. The earlier claim came from a grep
that filtered out lines containing "warning" and so mis-attributed an unrelated `error:` line. The
actual fatal diagnostic was the `namespace` variable (`CppNamespace`, an Error), fixed separately.

## Symptom
```
error: Common mistake detected: See error message for details
 73 |                 recovered_constants[SymbolId(id: const_idx)] = hir_const
Use <> instead of [] for generics
Old:     List[T]      New:     List<T>
```
`recovered_constants[SymbolId(id: const_idx)]` is a **dict index assignment whose key is a struct
literal**, not a generic type application. The heuristic fires on the shape
`identifier[Identifier(...)]` and cannot tell the two apart, so it rejects correct code with advice
that does not apply.

Same class as `namespace` being rejected as a variable name (fixed in this change by renaming the
variable at `src/lib/nogc_sync_mut/test_runner/test_runner_mcdc_report.spl:331`) and as the
already-fixed contextual-keyword family (`examples`, `and_then`, `move`, `admit`/`assume`).

## Scale
42 `Common mistake detected` sites in one `bin/simple test` run over clean `origin/main`, the first
in `src/compiler/20.hir/hir_lowering/_Items/module_build*.spl:73,81`.

## Fix direction
Only treat `X[Y]` as a generic when `Y` parses as a *type* and the construct is in type position;
a call/struct-literal argument list (`Ctor(field: expr)`) inside the brackets is a dict key, never
a generic parameter. Until then the detector must not be fatal — a heuristic hint that cannot be
suppressed and aborts the run is worse than no hint.


## Resolution

The rule fired on `identifier[` + any capitalized identifier, which is equally the shape of an
index whose key starts with a capital. Two discriminators were added, both of which can only ever
SUPPRESS a report (they never create one):

- **What follows the name.** A type list continues with `]` or `,` (`List[T]`, `Dict[K, V]`),
  while an index key continues with `(`, `.`, `[`, an operator, … — so
  `recovered_constants[SymbolId(id: const_idx)] = c` is recognised as an index.
- **The name's shape.** `SCREAMING_SNAKE_CASE` is a constant, never a type parameter, so
  `buf[MAX_LEN]` is an index.

`detect_common_mistake` keeps its three-token signature and delegates to a new
`detect_common_mistake_lookahead(current, previous, next, after_next)`; with `after_next: None`
the original behaviour is preserved, so the ~24 existing test call sites are untouched.

**The lookahead had to be lazy.** Buffering a second token eagerly in `advance()` broke five
`control_flow` inline-`match` tests: the lexer is context-sensitive, so pulling a token early
changes what it produces. The second token is therefore fetched only in the narrow shape that
could possibly report the mistake (`ident` `[` `CapitalizedIdent`).

### Evidence
- False generics warnings over one `bin/simple test` run of the compiler's own sources:
  **284 → 0**.
- `cargo test -p simple-parser`: `control_flow` back to `44 passed; 0 failed`; the whole suite is
  green except `test_val_match_keyword_is_rejected_but_contextual_distinctions_remain`, which is
  **pre-existing red on `origin/main`** (verified by running it with these three files reverted).
- New gate `parser/tests/wrong_brackets_index_false_positive.rs` — 4/4, and it pins BOTH
  directions: the three index shapes must stay silent and a genuine `List[T]` must still be
  reported, so the fix cannot be "achieved" by disabling the rule.
