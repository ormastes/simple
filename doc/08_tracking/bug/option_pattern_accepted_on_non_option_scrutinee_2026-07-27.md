# Bug: `Some(_)` patterns and `.unwrap_or` silently accepted on NON-Option values

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (silent wrong answers; type error degraded into bad data; engines disagree)
- **Found by:** lane OPTNIL, reproduced independently by the coordinator
- **Reconstructed:** the lane's original doc was clobbered off disk by a parallel
  session before landing; this is rewritten from the lane report plus the
  coordinator's own reproduction.

## Not what it first looked like

This was reported as "Option payloads bind as nil". That framing is **wrong** —
real `Option<T>` is correct on both engines for payloads `0, 1, 3, -7,
123456789`, across `match` / `if val` / `unwrap_or`, for
`Option<i64>`, `Option<text>` and `Option<struct>`. The prior-art
"JIT `Option<i64>` payload 3 reads as None" collision did **not** reproduce.

## The actual defect

`text.index_of` returns a **plain `i64`**, not `Option<i64>` — proven by
`idx + 1 == 7` with no unwrap. The compiler nonetheless **accepts `Some(_)`
patterns and `.unwrap_or` on non-Option receivers instead of erroring**.

A bare `val n = 6` reproduces every symptom with no `index_of` involved, so the
hole is in **type checking**, not in the producer. One raw value yields three
different wrong answers, because each consumer misdecodes the untagged scalar its
own way — and the two engines disagree:

| expression (`n` is a bare `i64` = 6) | JIT | interpreter |
|---|---|---|
| `match n: Some(i)` | takes the `Some` arm, binds **nil** | matches **neither arm — not even the `_` wildcard** |
| `n.unwrap_or(-99)` | **`<value:0x6>`** (tag box leaked into text) | `6` (returns the receiver) |
| `if val Some(k) = n` | branch **taken**, binds **nil** | not taken |
| bare `i64` passed through an `Option<i64>` **parameter** | binds **3** — a plausible wrong integer (`6>>1`) | falls through |
| `None.to_text()` | `nil` | **errors** |

The interpreter failing to match `_` is itself a second defect: a wildcard arm
must be unconditional.

## Where

- `src/compiler/10.frontend/core/interpreter/eval_methods.spl:107` — Option
  handling is gated on `kind == VAL_STRUCT`, so a raw `i64` misses every branch
  and `unwrap_or` (:117) falls through returning the receiver.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:388-396` —
  `option_payload_or_self` emits **`rt_unwrap_or_self`** ("return the receiver if
  it is not an Option"), typed `i64` while the value stays tag-boxed, producing
  `<value:0x6>`. Also :560, :598 and `cranelift_codegen_adapter.spl:1276`.

**That `_or_self` fallback is the design decision that converts a type error into
a silent wrong answer.**

## Blast radius

In owned `src/**`: 11,410 `Some(`, 911 `if val Some(`, 1,168 `.index_of(`.
**17 sites confirmed dangerous** — a bare-`i64` `index_of` result fed into an
Option form — including **4 in `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl`**.
Those 4 are the direct cause of the LLM lane's "every MCP tool argument silently
arrived empty" (`_extract_arg` returned `""` for every key). Causal chain closed.

## Reproduce

```
bin/simple run build/optnil_verify.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/optnil_verify.spl
```

## Interim mitigation

At the 17 sites, test `index_of`'s real `-> i64` contract directly:
`if i >= 0:` — do not destructure it as an Option.

## Why no fix landed

Tightening this changes compile behaviour at 11,410 `Some(` sites and needs a
staged warn→error migration; and the primary hole is in a compiler tree where
other lanes were live. A regression spec was also deliberately not added: it
would fail against `main` until the fix lands.

## Next step

1. Decide the contract: either `index_of` returns `Option<i64>` (and callers
   migrate) or it stays `i64` and Option forms on non-Option scrutinees become a
   **compile error**. The current middle ground is the bug.
2. Delete or gate `rt_unwrap_or_self` so a non-Option receiver is rejected rather
   than silently passed through.
3. Fix the interpreter's wildcard arm so `_` always matches.
4. Repair the 17 confirmed sites, starting with `jsonrpc.spl`.
