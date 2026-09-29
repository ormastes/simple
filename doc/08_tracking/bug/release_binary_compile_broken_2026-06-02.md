---
id: release_binary_compile_broken_2026-06-02
status: CLOSED (2026-09-13 triage)
severity: critical
discovered: 2026-06-02
discovered_by: MCP source fallback investigation
related: bin/release/x86_64-unknown-linux-gnu/simple
---

## Closed 2026-09-13 — Confirmed resolved: the deployed seed compiles and runs Simple sources

- **measured** `bin/simple --version` -> `Simple Language v1.0.0-rc.1`; `bin/simple run <hello-ish repro>` executes and prints program output (e.g. an array-push loop repro printing `100`).
- **measured** `bin/simple run` on a fresh 5-line source (`type Alias<T> = ...` + `print("ok")`) printed `ok`, so parse -> compile -> execute is intact end to end.
- **inferred** The entry's own frontmatter already recorded `RESOLVED-BY-REDEPLOY (2026-06-11)`; this run re-confirms it on the current binary. The separate self-hosted deploy remains tracked by the bootstrap effort, not by this entry.


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
