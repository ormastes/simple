# Seed interpreter: `match <i64>: Some(x)` binds a wrong value

- id: seed_match_some_on_plain_i64_binds_wrong_value_2026_11_12
- status: open
- severity: P2 (silent wrong value)
- found: 2026-11-12, lane work/t32-mcp-names-20261112
- binary: phase-1 seed sha256 9ce8892528f9397a58e1c1c6f5a68a43640121fb38c509780a5fa57457c27f2e

## Repro

```
fn main() -> i64:
    val json = "{\"value\":\"alpha\"}"
    val r = json.index_of("\"value\":")   # r prints 1
    var a = -1
    match r:
        Some(j): a = j
        nil: a = -2
    print "a={a}"                          # prints a=3, expected 1
    0
```

`text.index_of` returns a plain `i64` (-1 on miss). Matching it with
`Some(j)` should either bind 1 or be rejected; the seed binds 3.
`if val idx = r:` binds 1 correctly.

## Impact

`t32_extract_field` (t32_mcp/json_helpers.spl) returned `lpha"` for
`{"value":"alpha"}`. Workaround landed: use `t32_find_text`. Same pattern
remains in `examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl:116`.

## Fix direction

Either reject `Some(..)` against a non-Option scrutinee at check time, or make
the seed bind the payload the same way `if val` does.
