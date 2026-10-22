# String literal ending in `\"}}` loses one closing brace at compile time

- **Date:** 2026-09-25
- **Status:** open — worked around in `.spipe/spipe/src/spipe_mcp/main.spl` (`spm_init_json` carries a compensating extra `}`)
- **Severity:** P1 (silently corrupts string data; breaks JSON emitted by MCP servers)
- **Area:** seed compiler string-literal scanning/lowering (both JIT and interpreter paths of `bin/simple`, Sep 14 2026 build `src/compiler_rust/target/bootstrap/simple`)

## Minimal repro

```simple
extern fn print_raw(s: text)
fn main():
    print_raw("X\"}}")   # expected: X"}}  (4 chars)
    print_raw("\n")
    print_raw("Y\"}}Z")  # expected: Y"}}Z (5 chars)
    print_raw("\n")
```

Actual output (both `--mode=interpreter` and default JIT):

```text
X"}
Y"}}Z
```

The first literal loses one `}`. The corruption only triggers when the
literal ENDS with the sequence escaped-quote + two closing braces
(`\"}}` immediately before the closing quote). An interior occurrence
(`\"}}Z`) is unaffected.

## Impact

Any source that builds JSON (or other brace-heavy text) in a string literal
ending in `\"}}` emits malformed output with no error. Concrete instance:
`.spipe/spipe/src/spipe_mcp/main.spl` `spm_init_json` builds the MCP
initialize result; its literal ends `...\"}}"`, so the wire response was
missing the JSON-RPC envelope's final `}`, the MCP client failed
`initialize`, and the `spipe` MCP server reported "not connected".

A nasty second-order effect: SPEC ASSERTIONS are corrupted by the same bug,
so specs cannot reliably catch it. The assertion
`expect(r.stdout.trim().ends_with("\"}}}"))` compiles its pattern literal
`"\"}}}"` to `"}}` (one brace dropped), which happens to match the
corrupted output `...0.2.0"}}`, so the spec passes vacuously while the wire
format is broken. Always validate MCP/JSON wire output with an external
parser (e.g. python `json.loads`), never with spec-side string literals
containing the trigger sequence.

## Workaround

End such literals one brace earlier than the intended wire text (the
compiler drops one), or build the trailing braces via concatenation of
shorter literals / non-literal sources, or read the payload from a file
(only literal scanning is affected).

## Fix direction

Likely in the seed lexer/parser string-literal scanner: the escaped-quote
handling near end-of-literal apparently miscounts when followed by `}}`.
Repro belongs in `test/` for both the seed (Rust) and, once the pure-Simple
compiler hosts it, `src/compiler` frontend parity.
