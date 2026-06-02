---
id: release_binary_compile_broken_2026-06-02
status: OPEN
severity: critical
discovered: 2026-06-02
discovered_by: MCP source fallback investigation
related: bin/release/x86_64-unknown-linux-gnu/simple
---

# Release binary `compile` subcommand completely non-functional

## Summary

The self-hosted release binary `bin/release/x86_64-unknown-linux-gnu/simple`
(v0.4.0-beta.7, 33MB, May 31) fails to compile ANY source file including
`print "hello"`. The `compile` subcommand always produces:

```
error: parse error: Unexpected token: expected expression, found Newline
```

The interpreter/run mode works for simple files but is also degraded:
- Missing `rt_stdin_read_line` extern (needed by MCP servers)
- Does not support `\x` hex escape sequences in string literals

## Reproduction

```sh
echo 'print "hello"' > /tmp/test.spl
bin/release/x86_64-unknown-linux-gnu/simple compile /tmp/test.spl -o /dev/null
# error: parse error: Unexpected token: expected expression, found Newline
```

## Impact

- `bin/simple build bootstrap` cannot function (needs compile)
- MCP source fallback path broken (no interpreter stdin reading)
- All native compilation from source is non-functional via this binary

## Workaround

The Rust seed at `src/compiler_rust/target/bootstrap/simple` can compile files.
For MCP servers, the pre-compiled native binaries (Rust-compiled) work.
