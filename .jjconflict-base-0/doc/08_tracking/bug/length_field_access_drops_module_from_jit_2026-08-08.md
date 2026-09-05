# Field-style `.length` (and any unlowered field access on a builtin container) drops the whole module out of JIT

- Date: 2026-08-08
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- Severity: performance (~100-1000x on affected modules), silent for `.length` only

## Mechanism (reproduced independently)

`recv.length` with **no parens** parses as a FIELD access. HIR lowering has no
entry for it, so `src/compiler_rust/compiler/src/hir/lower/expr/access.rs:398`
raises `LowerError::Unsupported`, and the seed prints:

```
[jit-fallback] HIR lowering error: Unsupported feature: cannot infer field type
while lowering <fn>: struct 'Array' field 'length': whole module dropped to the
interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this
into a hard error.
```

Reproduced for **`Array`, `String` and `Dict`** receivers alike:

| receiver | `.length` (field) | `.length()` (method) |
|---|---|---|
| `[i64]`  | `[jit-fallback]` struct 'Array' field 'length', value still 3 | fine |
| `text`   | `[jit-fallback]` struct 'String' field 'length', value still 5 | fine |
| `Dict<text,i64>` | `[jit-fallback]` struct 'Dict' field 'length' | fine |

**The lane that swept `src/compiler` excluded text receivers on the stated
premise that "text routes through a different lowering path". That premise is
wrong** — text hits the identical error via the identical code path.

`"héllo".length` and `"héllo".len()` both return 6, so `.length` -> `.len()` on
text is semantics-preserving.

## Wider family

`.length` is not special to the lowering gap — **every** paren-less accessor on a
builtin container triggers the same fallback (`.len`, `.size`, `.empty`,
`.chars`, `.first`, `.last`, `.capacity` all probed, all emit `[jit-fallback]`).

But they are **not** the same severity, and the difference is the whole point:

| accessor | HIR lowering | interpreter | net effect |
|---|---|---|---|
| `.length` | fails -> module dropped | **accepts, correct value** | **SILENT**: only a perf loss, invisible in output |
| `.size`, `.empty`, `.chars`, `.first`, ... | fails -> module dropped | `error: semantic: undefined field: unknown property or method 'size' on Array` | self-reporting: the program dies |

So the wider family is real but self-announcing; `.length` is the single member
that is silent-and-correct, which is exactly why it accumulated to 384 sites
while the others did not accumulate at all.

## Scope (measured on origin/main)

384 field-style `.length` sites across `src/**/*.spl` (comment-stripped).

**How many are defects is NOT statically decidable, and that is itself the
finding.** Two successive filters give upper bounds of 254 and then 165 sites,
but both still over-report: `piece.length` in `src/app/svim/_SvimCore/text_ops.spl`
and `ref.length` in `src/app/interpreter/memory/refc_binary_spec.spl` are
genuine struct fields whose struct is *declared in a different file*. Deciding a
site needs the receiver's resolved type, i.e. it needs the compiler.

**Only the compiler's own `[jit-fallback]` diagnostic can enumerate this family
correctly** — a grep-based sweep will either miss sites or rewrite genuine field
accesses. Upper-bound distribution (165-filter), for sizing only:

| tree | upper-bound sites |
|---|---|
| src/lib/nogc_sync_mut | 28 |
| src/lib/gc_async_mut | 26 |
| src/unit/simple-lang | 24 |
| src/lib/nogc_async_mut | 22 |
| src/lib/skia | 11 |
| src/lib/common | 10 |
| src/app/interpreter | 8 |
| others | ~36 |

In `src/compiler` exactly **2** real sites remained after the earlier sweep
(both text receivers, both now fixed): `c_import_resolve.spl:36,38`. The other 6
`src/compiler` grep hits are docstrings (2) or genuine declared `length` fields
(`Span.length`, `StringTableEntry.length`).

## Why this keeps recurring

Nothing gates on it. `SIMPLE_JIT_STRICT=1` already exists and already turns the
fallback into a hard error, but no build or check invokes it, and no spec can
catch a perf-only defect. **Recommended fence:** a `scripts/check/*.shs` that
greps build/run stderr for `[jit-fallback]`, or that builds the tree under
`SIMPLE_JIT_STRICT=1`. Whack-a-mole by grep cannot close the family -- see Scope above.

## Do NOT mechanically rewrite Dict receivers

`.length` -> `.len()` is correct for Array and text receivers only. Per
`CLAUDE.md` (Native-Codegen Dict Pitfalls), `Dict.len()` returns **-1** under
native codegen. Dict sites need `keys().len()` or a maintained counter, so a
blanket sed would trade a perf defect for a wrong-value defect.

## Related, filed separately here for the record

`src/compiler/70.backend/backend/common/expression_evaluator.spl` is **dead and
unloadable**, and should be DELETED rather than maintained:

- it calls `literalconverter_convert_int/float/string/bool/nil/array/tuple/dict`
  — none of which are defined anywhere in `src/**/*.spl`;
- it constructs `BackendError.RuntimeError(..)`, which is not a variant of any
  `BackendError` enum (only used inside this one file);
- it declares `abstract class ExpressionEvaluator` with `extends` in its
  docstring, in a language with no inheritance;
- only `backend/common/mod.spl` (barrel re-export) and one census scan mention
  it — no real consumer.

Probed: `use compiler.backend.common.expression_evaluator.{Environment}` then
`Environment.create()` gives `Runtime error: Function 'create' not found`. The
class cannot be bound even by fully-qualified import, so **no spec can guard
it**. (Note: nothing binds at all — this is NOT a wrong-binding-to-a-same-named-
symbol defect.) Its `Environment` is now structurally identical to the live
`backend/env.spl` `Environment`, so deletion loses nothing.
