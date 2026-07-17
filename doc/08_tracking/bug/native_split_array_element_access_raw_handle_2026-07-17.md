# native-build: split()-result element access prints raw handle (silent wrong value)

**Severity:** high (silent wrong value)
**Found:** 2026-07-17 during review of the `text.split_lines()` fix lane
**Status:** open
**Backend:** pure-Simple `native-build --entry` MIR lowering / LLVM

## Symptom

Indexing an element out of a `text.split(...)` result and using it as text is
broken natively: printing yields a raw handle as a decimal integer, `.len()`
on an element SIGSEGVs, `==` comparison and `for`-in + concat produce garbage.
Array-level `.len()` on the split result is correct.

## Reproduction

```simple
fn main() -> i64:
    val parts = "aa,bb,cc".split(",")
    print(parts.len())
    print(parts[0])
    return 0
```

- Oracle (`env -u SIMPLE_BOOTSTRAP bin/simple run`): `3` then `aa`.
- Native (`native-build --entry ... --clean`, tip 5aee6bc6a25): `3` then a
  pointer-like decimal (observed `13575078161134`). Exit 0 — fully silent.

Same class reproduces for `lines[0].len()` (SIGSEGV) and
`for l in parts: joined = joined + l` (garbage decimals). Verified identical
behavior for `.split_lines()` results (same array representation and
`runtime_array_locals` routing), so this is generic to runtime string arrays,
not specific to either method.

## Hypothesis

Element loads from `runtime_array_locals`-flagged arrays go through
`rt_array_get` but the loaded element loses its str tag/type — downstream
consumers treat the handle as an integer (print-as-int) or as a raw pointer
(`.len()` SIGSEGV). Likely the element type is erased at the indexing site
(same "erased receiver/element type" family as
result_unwrap_receiver_type_erasure_2026-07-13.md, resolved) — the indexed
local needs to be registered as a tagged str (or the array's element type
threaded through) so string ops route via the str runtime path.

## Coverage gap

The native-seed parity harness (90 cases) does not cover split-element reads;
add a case when fixing (split + index + print + len + eq + for-in join).
