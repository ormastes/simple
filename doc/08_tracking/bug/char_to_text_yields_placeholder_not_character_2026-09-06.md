# `(N as char).to_text()` yields a placeholder string, not the character

Date: 2026-09-06
Status: OPEN
Area: runtime / char-to-text conversion (observed on the Rust bootstrap seed)

## Summary

`(123 as char).to_text()` does not produce `{`. It produces the **12-character
literal string** `<special:15>`. Likewise `(125 as char).to_text()` produces
`<value:0x7d>` rather than `}`.

This is a silent wrong-value bug, not a crash: the call succeeds, returns a
`text`, and every downstream consumer treats the placeholder as real content.

## Evidence

Binary under test:

```
readlink -f bin/simple
  -> bin/release/aarch64-unknown-linux-gnu/simple
bin/simple --version
  -> Simple Language v1.0.0-rc.1
     "this Rust-built Simple binary is a bootstrap seed only"
```

Probe wrote raw bytes to a file (deliberately not `print`, so no display layer
could be blamed) and the bytes were read back with `od -c`:

```
char_form_len=12 val=[<special:15>]     # (123 as char).to_text()
doubled_open_len=1 val=[{]              # "{{"
doubled_close_len=1 val=[}]             # "}}"
```

`od -c` confirms `char_form` is genuinely 12 stored characters — the length is
reported as 12 by `.len()`, so this is real string content, not a rendering
artifact.

The doubled-brace literal (`"{{"` / `"}}"`) is correct and yields exactly one
byte. That is already this repo's established escape convention for a literal
brace inside an interpolating string — see `PANE_FORMAT` in
`src/app/llm_caret/pane_backend.spl`, which writes `#{{pane_id}}` to emit
`#{pane_id}`.

## Impact found in the field

Every JSON producer in `src/app/llm_caret/` had inlined the broken form as its
`_LB()` / `_RB()` brace helpers — **22 occurrences across 11 files**
(`server.spl`, `chat.spl`, `tools.spl`, `mod.spl`, `claude_api.spl`,
`openai_api.spl`, `openai_compat.spl`, `claude_cli.spl`, `infra_mail.spl`,
`infra_storage.spl`, `infra_wiki.spl`).

Consequence: every JSON envelope caret emitted was **malformed at byte 0**, e.g.
the health endpoint wrote

```
<special:15>"status":"ok",...<value:0x7d>
```

instead of `{"status":"ok",...}`. The caret HTTP server therefore could not have
been consumed by any real client.

Why it was never caught: the unit specs
(`test/01_unit/app/llm_caret/server_spec.spl`,
`test/unit/app/llm_caret/server_spec.spl`) define their own **local copies** of
the response builders rather than importing the real ones, and assert only on
substrings (`contains("chat.completion")`), which pass just as happily on a
malformed envelope. No assertion ever checked that the output was valid JSON.

## Repair applied to the call sites

The 22 caret call sites were changed to the doubled-brace literals and the real
builders now emit output that a real JSON parser accepts:

```
{"id":"chatcmpl-llm_caret","object":"chat.completion","model":"claude-sonnet-5",
 "choices":[{"index":0,"message":{"role":"assistant","content":"PONG"},
 "finish_reason":"stop"}]}
-> json.loads(): VALID
```

That repairs the symptom in caret. **It does not fix the underlying conversion**,
which is why this record exists.

## What still needs deciding

`(N as char).to_text()` is a short, natural expression form that silently
returns wrong data. Per the project rule against normalizing a workaround, the
conversion itself should either:

1. produce the actual character for a valid code point, or
2. fail loudly (compile error or runtime error) if the form is not supported,

rather than returning a placeholder that looks like a successful conversion.

Open questions for whoever picks this up:

- Which layer emits `<special:15>` / `<value:0x7d>`? The `15` and the `0x7d` are
  formatted differently from each other, which suggests two distinct fallback
  paths rather than one.
- Does the same defect reproduce on a self-hosted (non-seed) binary? Not
  verifiable here — no self-hosted `bin/release/<target>/simple` exists on this
  host, so only the seed was measured. **Re-verify before assuming the scope.**
- Are there other `as char` conversions in the tree relying on this? The caret
  sweep covered `src/app/llm_caret/` only; a repo-wide audit of `as char` was not
  done.

## Reproduce

```spl
use std.nogc_sync_mut.fs.{write_file}

fn main():
    val a = (123 as char).to_text()
    write_file("out.txt", "len=" + a.len().to_text() + " val=[" + a + "]\n")
```

```
bin/simple run probe.spl && od -c out.txt
```

## Triage 2026-09-12
Remediation 2026-09-12: an earlier automated pass matched a spec path mentioned in this record and ran it, but on review that spec was not clearly this record's own reproduction (see evidence); the RESOLVED/still-reproduces verdict was withdrawn. Record postdates 2026-07-29, so it is left open rather than closed.

## Triage 2026-09-12 — root cause located, still OPEN (needs a Rust seed change)

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, sha256
prefix `3d120a6f`).

### Reproduced, and widened

```spl
val a = (123 as char).to_text()   # a_len=12  a=[<special:15>]
val b = (125 as char).to_text()   # b_len=12  b=[<value:0x7d>]
val c = (65  as char).to_text()   # c_len=19  c=[<invalid-heap:0x41>]
```

### Root cause

The three different placeholder shapes are not three fallback paths — they are
**one** defect seen through three tag values. `(N as char)` emits the raw
machine scalar `N` where a *tagged* `RuntimeValue` word is expected, so
`rt_to_string` decodes `N`'s own low 3 bits as the tag:

| N | N & 7 | tag | payload (N >> 3) | rendered |
|---|-------|-----|------------------|----------|
| 123 | 3 | TAG_SPECIAL | 15 | `<special:15>` |
| 125 | 5 | (no such tag) | — | `<value:0x7d>` |
| 65  | 1 | TAG_HEAP | 0x41 as a pointer | `<invalid-heap:0x41>` |

That is exactly the `value_to_display_string` match in
`src/compiler_rust/runtime/src/value/sffi/io_print.rs:452-466`
(`TAG_SPECIAL` arm -> `<special:{p}>`, `_` arm -> `<value:0x{:x}>`,
`heap_value_to_display_string` -> `<invalid-heap:0x{:x}>` when `heap_type()`
is `None`). The renderer is behaving correctly on the garbage it is handed.

The garbage is produced one layer up, in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs:549`
`lower_cast_expr`. It has exactly one special case — `target == TypeId::STRING
&& is_native_scalar(inner.ty)` routes to `emit_to_string` — and the comment
there states the general hazard verbatim: *"MirInst::Cast is a plain value copy
in codegen, so a raw int/float would masquerade as a STRING pointer"*. A cast
to `char` takes the fall-through branch and emits a bare `MirInst::Cast`, i.e.
the plain value copy, with no boxing or tagging.

`is_native_scalar` (same file) lists I8..U64, F32/F64, BOOL — it does not list
CHAR, and nothing else in the function distinguishes CHAR.

### Fix direction

Give `char` the same treatment `STRING` already has in `lower_cast_expr`:
an int -> char cast must yield a properly tagged `RuntimeValue` (or, if `char`
has no tagged representation, `to_text()` on it must route to a real
`rt_char_to_string`-style conversion that builds the 1-code-point string),
instead of a plain value copy. Whichever is chosen, the *other* branch of the
original bug report still applies: if the form cannot be supported it must fail
loudly rather than return a placeholder.

### Why this is not fixed in this pass

The change is in the Rust bootstrap seed
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`), and the fan-out
lane's bar is "GREEN unit specs on the deployed binary". Fixing the seed source
cannot be demonstrated green without rebuilding and redeploying `bin/simple`,
which this lane is explicitly forbidden to do. No permanently-red spec was added,
per the project rule against landing a failing test.

Open sub-question still unanswered: whether the pure-Simple mirror
(`src/compiler/50.mir/**` cast lowering) carries the same gap. It was not
audited here, and it is the path that matters once a self-hosted binary is
deployed.

## Triage 2026-09-13 (BUGFIX-7 lane) — reconfirmed on `a6450c9d6f5`, pure-Simple mirror audited

Re-ran the exact repro from this record on `bin/simple run` (deployed Rust seed,
`bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`) at
`a6450c9d6f5` — identical output byte-for-byte to the 2026-09-12 triage
(`a_len=12 [<special:15>]`, `b_len=12 [<value:0x7d>]`, `c_len=19
[<invalid-heap:0x41>]`). Still reproduces; not a regression, not fixed.

Answered the open sub-question: the pure-Simple mirror
`me lower_cast_expr` at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2277-2330` has the
**same structural gap**, and arguably a *wider* one — it has no `STRING`
special case either (unlike the Rust seed's `lowering_expr_ops.rs`, which at
least special-cases `target == TypeId::STRING`). Every branch in this function
ends at `cast_builder.emit_cast(mir_operand_copy(operand_local), mir_target)`
(line 2328) — the same "plain value copy" the Rust bug record identifies as
the defect — for every scalar cast target, `char` included, with no boxing or
tagging step and no dedicated `emit_to_string`-style helper anywhere in this
file (`grep -n "emit_to_string" expr_dispatch.spl` — 0 hits).

This CANNOT be turned into a demonstrable RED->GREEN unit spec by this lane:
this pure-Simple source is the self-hosted compiler's own MIR lowering, only
exercised end-to-end by a self-hosted `bin/release/<target>/simple` running
`native-build`/`compile`. No such binary exists on this host or in this
worktree (only the Rust seed, confirmed via `bin/simple --version` printing
"bootstrap seed only"), so a spec that drives this code path would either (a)
not execute it at all (falling through to the seed's own Rust codegen, which
is a different implementation entirely), or (b) require standing up a
self-hosted deploy first — out of scope for this lane (no bootstrap, per the
fan-out brief). Left OPEN, no code change made. Whoever next has a self-hosted
binary should: write the reproduction as a `.spl` fixture, run it through
`bin/simple native-build`/`compile` on that binary, confirm the same
`<special:N>` / `<value:0xNN>` shape, then fix `lower_cast_expr` to special-case
`char` (and audit whether `STRING` needs the same treatment there, since this
mirror lacks even that).
