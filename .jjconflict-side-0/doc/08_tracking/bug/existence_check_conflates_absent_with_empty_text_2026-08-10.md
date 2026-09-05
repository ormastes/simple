# `.?` cannot distinguish an ABSENT key from a key present with an empty `text`

**Status:** CLOSED — NOT A DEFECT. Misdiagnosis: `.?` folding empty
`text`/`[T]`/`{K:V}` into `nil` is DOCUMENTED, INTENTIONAL behavior, consistent
across four separate call-outs in the same reference doc this bug quoted from.
Re-triaged 2026-08-10 while attempting the fix this doc calls for.
**Filed:** 2026-08-10
**Found by:** Q31.
**Closed by:** re-triage, 2026-08-10 (see "Re-triage" below).

## Re-triage finding

The "Documented semantics" section below quotes
`doc/07_guide/quick_reference/syntax_quick_reference.md:552` ("Returns `T?` …
the value itself if present, `nil` if absent") but **omits the parenthetical
one line above it, line 548**, which is the actual definition of "present"
being used:

> ### Existence Check (`.?`) — Returns `T?`
>
> The `.?` operator checks if a value is **present (not nil AND not empty)**.

That "AND not empty" clause is not a slip — it is restated three more times in
the same file:
- line 567: `list.? # [T]?: Some(list) if non-empty, nil if []`
- line 568: `dict.? # {K:V}?: Some(dict) if non-empty, nil if {}`
- line 569: `str.? # text?: Some(str) if non-empty, nil if ""`
- line 1062: `x.? # Existence check (is present/non-empty)`

And the doc explicitly documents the ASYMMETRY the bug report's "Scope"
section asked to have checked: primitives are exempted from the emptiness
fold —
- line 570: `num.? # i64?: Some(num) — primitives always present`
- line 571: `flag.? # bool?: Some(flag) — primitives always present`

`src/compiler_rust/compiler/src/interpreter/expr.rs` (`Expr::ExistsCheck`,
~line 503) implements exactly this: `Value::Str`/`Value::Array`/`Value::Dict`
fold emptiness into absence; every other payload kind (`Int`, `Bool`, `Float`,
structs, ...) falls through the `_ => true` arm and is always present
regardless of value. That is not a bug living "one level down" from the
`Some(0)`/`Some("")` truthy-payload trap this doc invoked — it is the CORRECT,
deliberate implementation of the documented split.

Reproduced directly against `bootstrap/stage3/simple` (today's pure-Simple
self-hosted build) via `bin/simple test` (the same execution mode
`app_mcp_intensive_spec` runs under): `expect(d["k"].? != nil).to_be(true)`
for `d = {"k": ""}` correctly fails, and it SHOULD fail per spec — an empty
`text` is documented-absent under `.?`. A plain interpreter run
(`bin/simple run`) of the equivalent code (not through the spec/matcher
pipeline) also agrees. No engine divergence, and no defect: both lanes
implement the documented fold.

## Correction to "Impact"

The 9 `.? != nil` rewrite sites listed below (`version`, `id`, `method`,
`code`, `message`, `target`, `release`, `args`, `revision`) are **not** "safe
by luck". `.? != nil` on those fields means "present AND non-empty", which is
the intended/desired validation for required protocol fields — an
empty-but-technically-present `version` string would be exactly as wrong for
those call sites as a missing one, so folding the two together is the correct
check, not a latent landmine. No change needed at those 9 sites. If a future
field can be *legitimately* empty AND the check must still distinguish
"key present" from "key absent" regardless of emptiness, the correct primitive
is dict presence (e.g. `d.contains("k")` / `.has()`), not `.?` — `.?` was
never a raw Option/key-presence unwrap; it is documented as a presence+
non-emptiness convenience operator.

## Disposition

No code change made. `.?`'s empty-`text`/`[T]`/`{K:V}` folding is left as
documented, deliberate behavior — changing it would silently break every
other call site in the codebase relying on `str.?`/`list.?`/`dict.?` meaning
"non-empty", which is the documented contract, not an incidental
implementation detail. Do not re-open this as a `.?` defect; if the "key
present vs absent, ignoring emptiness" semantics are wanted at a call site,
use `.contains()`/`.has()` instead.

## Documented semantics (as originally filed — kept for context; see
## "Re-triage finding" above for the correction)

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

## Unblock condition (superseded — see "Disposition" above)

Originally: "`.?` on a present key with an empty `text` payload returns that
empty text, not `nil`, on all three lanes; and the same is verified for
numeric `0` and `false`." Superseded: `.?` returning `nil` for empty
`text`/`[T]`/`{K:V}` is the documented, correct behavior and is NOT to be
changed. Numeric `0` / `false` are already verified always-present, matching
spec (`syntax_quick_reference.md:570-571`) and the `expr.rs` `_ => true`
fallthrough.
