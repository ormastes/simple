# Native lane: optional-tuple payload extraction is broken in every consumption form

**Status:** open — isolated with a 30-line repro while typing the MQTT packet
module (`mqtt/packet.spl`) for native compilation.
**Severity:** silent wrong results / silently skipped control flow on the
DEFAULT engine (`bin/simple run`, JIT/native — no interpreter fallback and no
diagnostic). Blocks the MQTT decode round-trip on the default engine even
though the module now compiles natively.

## Repro (fully typed, compiles natively, no HIR fallback)

```
fn f(flag: i64) -> (text, i64)?:
    if flag == 0:
        return nil
    ("x", 7)

fn g(flag: i64) -> (i64, i64)?:
    if flag == 0:
        return nil
    (5, 9)

fn main():
    if val Some(p) = f(1):
        print "F1_SOME: {p.0} {p.1}"
    else:
        print "F1_NONE"
    if val Some(q) = f(0):
        print "F0_SOME_BUG"
    else:
        print "F0_NONE_OK"
    match g(1):
        Some(t):
            print "G1_SOME: {t.0} {t.1}"
        nil:
            print "G1_NIL"
    val r = g(1)
    if r == nil:
        print "R_EQ_NIL"
    else:
        print "R_NOT_NIL"
```

Observed on the deployed seed (2026-07-29, `bin/simple run`, native — verified
no JIT-fallback INFO line):

| Construct | Expected | Observed |
|---|---|---|
| `if val Some(p) = f(1)` (value IS Some) | F1_SOME: x 7 | **NEITHER arm runs** — both silently skipped |
| `if val Some(q) = f(0)` (value is nil) | F0_NONE_OK | F0_NONE_OK (correct) |
| `match g(1): Some(t)` | G1_SOME: 5 9 | **G1_SOME: 3 3** — both payload fields read as 3, the nil sentinel |
| `r == nil` on a Some value | R_NOT_NIL | R_NOT_NIL (correct) |

So nil-detection works, but PAYLOAD EXTRACTION does not: the if-val-Some form
skips both branches for a genuine Some, and the match form takes the right arm
but yields sentinel-3 garbage for every field. Same family as the known
"JIT Option<i64> payload-3 == nil collision" and "?? on raw i64 corrupts"
sentinel bugs, but here the whole tuple payload is unrecoverable in every
consumption form tried. The interpreter lane extracts these payloads
correctly (verified: the same optional-tuple `== nil` check plus `.0`/`.1`
reads through the MQTT module ran correctly whenever the module fell back to
the interpreter).

## Impact example

`src/lib/nogc_sync_mut/mqtt/packet.spl` (+ mirrors) decode functions return
`(text, i64)?` / `(i64, i64)?` / `([i64], i64)?`. After typing the module so
it compiles natively (it previously fell back whole-module to the interpreter
over untyped parameters), the native encode path is byte-exact
(`mqtt_encode_string("café") -> [0, 5, 99, 97, 102, 195, 169]`), but no
caller can extract the decode results natively — the round-trip is blocked on
this defect, not on the MQTT logic, which is correct in isolation.

## Notes

- Do NOT work around by restructuring decode return contracts module-by-
  module; fix the codegen.
- Any module returning optional tuples that newly gains native compilation
  (e.g. by adding type annotations) is exposed; the interpreter fallback was
  masking this.
