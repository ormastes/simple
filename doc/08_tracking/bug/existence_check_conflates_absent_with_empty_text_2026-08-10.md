# `.?` cannot distinguish an ABSENT key from a key present with an empty `text`

**Status:** OPEN — genuine defect, found while triaging the `app_mcp_intensive_spec` `.?` failures.
**Filed:** 2026-08-10
**Found by:** Q31.

## Documented semantics

`doc/07_guide/quick_reference/syntax_quick_reference.md:552` — Existence Check
(`.?`) "Returns `T?` … the value itself if present, `nil` if absent". It is a
**presence** test that yields a payload, not a predicate.

## Symptom

For a value that IS present but whose payload is an empty `text`, `.?` yields
`nil` — i.e. it reports **absent**.

```simple
val d: {text: text} = {"k": ""}
expect(d["k"].? != nil).to_be(true)      # FAILS -- reports nil
```

Measured (interpreter and JIT agree; no engine divergence):

| receiver | `.?` result |
|---|---|
| `d["k"]` where `d = {"k": "v"}` | `"v"` (present) |
| `d["nope"]` (missing key) | `nil` (absent) — correct |
| `d["k"]` where `d = {"k": ""}` | **`nil`** — WRONG, the key is present |
| local `text` `s = "world"` | `"world"` |
| local `text` `e = ""` | **`nil`** |
| `5.?`, `true.?` | `5`, `true` |

So the empty `text` is being folded into the absent case. Presence and emptiness
become indistinguishable, and `.? != nil` — the natural predicate spelling — is
wrong for any field that may legitimately be empty.

This is the mirror image of the documented `Some(0)`/`Some("")` truthy-payload
trap: the trap warns that a *falsy payload is still present*, and here the
implementation is making exactly the mistake the trap warns about, one level
down.

## Scope

`text` specifically. `5.?` and `true.?` return their values, so `0.?` /
`false.?` should be checked for the same collapse when this is fixed — the
family has not been enumerated for numeric zero and `false` yet, and it should be
before this is closed.

## Impact

Any presence check over a dict of `text` silently misreports empty-string values
as missing. The `app_mcp_intensive_spec` fields fixed in this session
(`version`, `id`, `method`, `code`, `message`, `target`, `release`, `args`,
`revision`) are all non-empty in practice, so their `.? != nil` rewrite is
correct — but that is luck, not safety, and any future field that can be empty
will silently assert the wrong thing.

## Not to be confused with

The 10 `expect(dict_value.?).to_be(true)` assertions in `app_mcp_intensive_spec`
were plain **spec misuse** — `.?` returns the payload, so the matcher was
correctly reporting the underlying text against `true`. That is fixed separately
and is NOT this defect. This defect is the empty-`text` collapse only.

## Unblock condition

`.?` on a present key with an empty `text` payload returns that empty text, not
`nil`, on all three lanes; and the same is verified for numeric `0` and `false`.
