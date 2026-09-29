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
