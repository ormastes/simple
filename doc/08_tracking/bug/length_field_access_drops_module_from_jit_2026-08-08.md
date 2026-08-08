# Field-style `.length` (and any unlowered field access on a builtin container) drops the whole module out of JIT

- Date: 2026-08-08
- Status: OPEN (partial fix landed for `src/compiler`)
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
`.chars`, `.first`, `.last`, `.capacity` all probed and all emit
`[jit-fallback]`). `.length` is only special in that the **interpreter** accepts
it and returns the correct value, so it is the one member of the family that is
completely invisible in program output. The others also produce a runtime error,
so they self-report.

## Scope (measured on origin/main)

384 field-style `.length` sites across `src/**/*.spl` (comment-stripped).
254 of them live in files that declare no `length` struct field at all:

| tree | suspect sites |
|---|---|
| src/os/port | 61 |
| src/lib/nogc_sync_mut | 33 |
| src/lib/nogc_async_mut | 28 |
| src/lib/gc_async_mut | 27 |
| src/unit/simple-lang | 24 |
| src/lib/skia | 11 |
| src/app/svim | 11 |
| src/lib/common | 10 |
| others | ~49 |

In `src/compiler` exactly **2** real sites remained after the earlier sweep
(both text receivers, both now fixed): `c_import_resolve.spl:36,38`. The other 6
`src/compiler` grep hits are docstrings (2) or genuine declared `length` fields
(`Span.length`, `StringTableEntry.length`).

## Why this keeps recurring

Nothing gates on it. `SIMPLE_JIT_STRICT=1` already exists and already turns the
fallback into a hard error, but no build or check invokes it, and no spec can
catch a perf-only defect. **Recommended fence:** a `scripts/check/*.shs` that
greps build/run stderr for `[jit-fallback]`, or that builds the tree under
`SIMPLE_JIT_STRICT=1`. Whack-a-mole across 254 sites will not close the family.

## Do NOT mechanically rewrite Dict receivers

`.length` -> `.len()` is correct for Array and text receivers only. Per
`CLAUDE.md` (Native-Codegen Dict Pitfalls), `Dict.len()` returns **-1** under
native codegen. Dict sites need `keys().len()` or a maintained counter, so a
blanket sed would trade a perf defect for a wrong-value defect.
