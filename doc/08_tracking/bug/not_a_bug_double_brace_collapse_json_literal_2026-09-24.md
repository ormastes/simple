# Not a bug: `}}`/`{{` collapse to one literal brace in Simple string literals

**Status: closed, no code change.** Filed to record the investigation and stop
a recurring "Windows write path drops a `}`" misdiagnosis.

## Reported symptom

A previous agent working on
`test/02_integration/app/spipe/spipe_mcp_node_fallback_crlf_windows_spec.spl`
reported: "writing a JSON string literal ending in 3+ consecutive `}` before
`\r\n` silently drops one `}` on this host's write path — reproduced twice,
worked around in the new spec." The spec's `it "returns a JSON-RPC error with
a non-null id..."`, `"...missing required params"`, `"...missing file/path
argument"`, and `"...very long single input line..."` cases write JSON with a
space inserted between consecutive closing braces (`{} } }` instead of
`{}}}`) — that spacing is the undocumented workaround.

## Root cause: NOT the write path, NOT CRLF, NOT Windows

Reproduced with the deployed seed
`bin/release/x86_64-pc-windows-msvc/simple.exe` using nothing but `print()` —
no file write, no CRLF, no `\r\n`, no process pipe:

```
val s3 = "{\"a\":{}}}"      # 3 closing braces -> printed len=8, expected 9
val s4 = "{\"a\":{}}}}"     # 4 closing braces -> printed len=9, expected 10
val s5 = "{\"a\":{}}}}}"    # 5 closing braces -> printed len=9, expected 11
```

The byte loss happens at **lex time**, in
`src/compiler_rust/parser/src/lexer/strings.rs:463-475`, in the double-quoted
(f-)string scanner:

```rust
} else if ch == '}' {
    self.advance();
    // Check for escaped }} -> literal }
    if self.check('}') {
        self.advance();
        current_literal.push('}');
        current_literal_raw.push_str("}}");
    } else {
        // Treat single } as literal } (lenient mode)
        current_literal.push('}');
        current_literal_raw.push('}');
    }
}
```

This is **documented, intentional** behavior, not a defect: the block above
it (lines 176-183) states "`{{`/`}}` collapse to a single literal brace in
EVERY double-quoted text literal, interpolated or not," citing
`runtime_surface_spec_brace_escape_contains_red_2026-08-17.md` and pinned by
`src/compiler_rust/parser/src/lexer_tests_literals.rs::double_braces_collapse_to_one_literal_brace`.
It mirrors Python f-string escaping (`{{` -> `{`, `}}` -> `}`) and is applied
unconditionally, even to strings with no interpolation, so a raw JSON literal
with two or more adjacent `}` is silently re-encoded: pairs of `}` collapse
pairwise left-to-right, with any leftover single `}` passed through literally.
An immediately-preceding `{}` (empty-object shortcut, ~line 430-440) consumes
one `}` on its own, which is why a lone `"params":{}}` (net 2 closing braces)
survives untouched — it's exactly 3+ *net* consecutive closing braces after
any leading `{}` that lose a byte.

No runtime `rt_*` write function, no MSYS/Git Bash layer, and no Node reading
side are involved; the string is already short by the time it reaches
`write_file`/`run`/stdout.

## Verdict on the spec's workaround

`spipe_mcp_node_fallback_crlf_windows_spec.spl`'s spacing (`{} } }`) is a
correct and reasonable way to avoid the collapse in a hand-written JSON
literal, and should stay — inserting a space breaks the `}}`-adjacency the
lexer is scanning for. The spec carries no inline comment mischaracterizing
this as a write-path/CRLF/Windows bug (checked line-by-line against
`origin/main`), so there is no incorrect "bug" claim in-file to correct.

## Disposition

No code change proposed. If the language wants a friendlier way to author
literal JSON strings, the existing raw-string form (`r"..."`, no escapes, no
interpolation, `strings.rs:53`) is the intended escape hatch — note it also
does not support `\"`, so raw JSON with embedded quotes needs single-quoted
raw strings or concatenation. That ergonomics gap (JSON literals in
interpolated double-quoted strings) is not tracked as a separate feature
request here; file one only if it recurs and someone wants the ergonomics
improved.
