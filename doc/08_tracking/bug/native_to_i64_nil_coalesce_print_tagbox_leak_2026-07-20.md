# Native `text.to_i64() ?? default` leaks tag-box representation, wrong value in string interpolation

**Date:** 2026-07-20
**Status:** OPEN — found incidentally while instrumenting an unrelated bug
(`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`), not
independently bisected further; filed per repo rule (concrete bug over
silent workaround) rather than tracked only as a doc aside.
**Severity:** P2 — silent wrong value, no diagnostic, on a common stdlib
call (`text.to_i64()` combined with `??` and string interpolation).
**Component:** compiler codegen — Option (`i64?`) coalesce (`??`) +
string-interpolation print, **hosted native-build**
(`x86_64-unknown-linux-gnu`, cranelift backend, `--mode one-binary`).
Same "Some payload not correctly unwrapped/reboxed" family as
[hosted_native_option_try_unwrap_payload_leak_2026-07-19](hosted_native_option_try_unwrap_payload_leak_2026-07-19.md),
different shape (`??` + print-interpolation, not `.?`/`if val`).

## Symptom

```simple
fn main() -> i64:
    val s = "12345"
    val n = s.to_i64() ?? -999
    print "n={n}"
    val s2 = "12345".trim()
    val n2 = s2.to_i64() ?? -999
    print "n2={n2}"
    0
```

Compiled via `native-build --source . --entry t.spl --backend cranelift
--mode one-binary` on the stage3 self-hosted binary
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`) and run:

```
n=<value:0x3039>
n2=341095809
```

Expected `n=12345` / `n2=12345`. Two distinct wrong outputs from the same
source value:

- `n`: prints the raw tagged/boxed representation `<value:0x3039>` instead of
  being unwrapped to a plain `i64` for string interpolation. Note `0x3039 ==
  12345` — the correct integer **is** inside the box, so `to_i64()`/`??`
  itself produced the right payload; the bug is in how `{n}` interpolation
  reads/formats an `i64` that arrived via `text.to_i64() -> i64?` + `??`
  coalesce (the interpolation code path apparently doesn't unbox it before
  formatting, or picks the wrong print-dispatch arm for a still-tagged
  value).
- `n2` (same literal, routed through `.trim()` first): prints a *different*
  wrong integer (`341095809`) rather than the boxed-tag string seen for
  `n`. Not reproduced deterministically across sessions — an earlier probe
  in the same investigation (via a `rt_process_run`-sourced string, not a
  literal) saw `675995905` for the same `"12345".trim().to_i64()` shape.
  The non-constant wrong value suggests uninitialized/misinterpreted memory
  being read back as the payload, not a fixed miscompile constant — consistent
  with a box/unbox or ABI mismatch rather than an arithmetic error in
  `to_i64` parsing itself.

## Why this isn't the parse-memory bug it was found investigating

Confirmed isolated from `rt_process_run`, from `--low-memory`, and from any
of that investigation's driver.spl changes — reproduces on a two-line
`main()` with only stdlib calls, no extern declarations, no other project
code involved. Purely a `to_i64()` + `??` + print-interpolation codegen
question.

## Root cause

Not bisected. Likely the same box/unbox family flagged in
`hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`'s "Related /
class" section (`box_enum_payload_if_needed` gating, `rt_enum_payload`
extract/unbox path shared across Option shapes) — that doc's repro is
`.?`/`if val`; this one is `??` + print, a different lowering surface that
may share the same underlying Option-ABI representation bug. Needs its own
bisection before assuming it is the exact same root cause.

## Repro

```sh
SB=build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
mkdir -p /tmp/toi64repro && cd /tmp/toi64repro
cat > t.spl <<'EOF'
fn main() -> i64:
    val s = "12345"
    val n = s.to_i64() ?? -999
    print "n={n}"
    val s2 = "12345".trim()
    val n2 = s2.to_i64() ?? -999
    print "n2={n2}"
    0
EOF
"$SB" native-build --source . --entry t.spl --backend cranelift --mode one-binary -o out
./out   # expect n=12345 / n2=12345, observe n=<value:0x3039> / n2=<garbage>
```

Not yet added to `scripts/check/native-smoke-matrix.shs` — future session
should add a case here (matching the `optnil` case style in the sibling bug
doc) once this is bisected enough to know the expected fix shape.
