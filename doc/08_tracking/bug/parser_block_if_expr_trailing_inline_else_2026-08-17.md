# Block-form `if` expression rejects a trailing inline `else:` on the branch body line

**Date:** 2026-08-17
**Status:** OPEN
**Severity:** MEDIUM — `src/lib/hardware/rv64gc_rtl/imac_protected_core.spl` and
`src/lib/common/crypto/x25519_mlkem768/matrix_receipt.spl` (and every module
importing them) fail to parse
**Found by:** `src/lib/**` parse sweep (7780 files, complete)
**Binary:** `/mnt/data/cgtw2/release/simple` (freshly built Rust seed) — also
fails on the stale deployed binary, so this is not a fresh-build regression

## Minimal reproduction

FAILS — the `if` header opens a block, and the branch body line carries the
`else:` inline at its end:

```simple
fn a4(p: i64, lo: i64) -> i64:
    val v = if p == 1:
        lo else: 9
    v
```

```
error: compile failed: parse: Unexpected token: expected expression, found Else
```

PASSES — same expression with `else:` moved onto its own line at the `if` indent:

```simple
fn a3(p: i64, lo: i64) -> i64:
    val v = if p == 1:
        lo
    else: 9
    v
```

Both the fully-inline form (`val v = if p == 1: lo else: 9`) and the fully-block
form parse; only the mixed form — block-opened header, inline `else` trailing the
indented branch body — is rejected.

## Real-world site

`src/lib/hardware/rv64gc_rtl/imac_protected_core.spl:529-531`:

```simple
            val fault_insn = if state.pipeline_phase == CORE64_FETCH_HIGH:
                state.fetch_low else if state.pipeline_phase == CORE64_FETCH_LOW:
                0 else: state.instruction
```

## Second route: via `elif` (found in the sweep tail, 2026-08-17)

The completed sweep found a second root with the same root cause, reached
through `elif` rather than a plain `if` branch. FAILS:

```simple
fn e1(a: bool, r: text) -> text:
    val v = if a: "" elif r != "":
        r else: "z"
    v
```

PASSES with `else:` moved to its own line:

```simple
fn e2(a: bool, r: text) -> text:
    val v = if a: "" elif r != "":
        r
    else: "z"
    v
```

Real site — `src/lib/common/crypto/x25519_mlkem768/matrix_receipt.spl:697-698`:

```simple
        val admission_reason = if admitted_row: "" elif reason != "":
            reason else: "source-row-public-output-mismatch"
```

So the defect is not specific to `if`/`else if`: any branch body that is opened
as an indented block and then carries a trailing inline `else:` is rejected.

## Expected

`else` / `else if` terminates the current branch body wherever it appears, the
same way it does when it starts a line. The parser currently only recognises it
in statement-leading position after a dedent.

## Not worked around

The source was deliberately left unchanged so the repro survives; this is the
same continuation-line-indentation family as
`parser_same_indent_leading_operator_continuation_2026-08-17.md` and
`stage2_multiline_if_continuation_2026-08-14.md`.
