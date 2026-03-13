# cmm-lsp

TRACE32 PRACTICE/CMM language server plugin for Claude Code.

Runtime:

```bash
bin/release/simple examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp
```

## Common CMM Mistakes

### Lexer Ambiguities

| Pattern | Trap | Correct Interpretation |
|---------|------|----------------------|
| `&name` vs `&0xFF` | `&` is both macro ref AND bitwise AND | `&` + letter = macro; `&` + digit = AND + hex |
| `*` wildcard vs multiply | `&a*&b` is multiply; `Data.LOAD.auto *` is wildcard | Trailing `*` = wildcard |
| `/Word` vs `path/file` | `/` is both option flag AND path separator | After command = option; in path context = separator |
| `%val%100` vs `%LE` | `%` is both modulo AND format spec | `%` + uppercase = format; `%` + value = modulo |

### Statement-Level Gotchas

| Mistake | What Happens | Fix |
|---------|-------------|-----|
| `&cmd` on its own line | Executes macro value as command | Use `&cmd="value"` for assignment |
| `ON ERROR` without action | Clears the error handler | Add `GOTO`/`GOSUB` for a handler |
| Missing `ENDDO` | Script runs past intended end | Always end scripts with `ENDDO` |
| `GOTO` without target | Clears GOTO target | Add label: `GOTO mylabel` |

### Numeric Literal Traps

| Literal | Value | Trap |
|---------|-------|------|
| `100` | Radix-dependent! | May be hex! Use `100.` for decimal or `0x64` for hex |
| `0y10110` | Binary (22) | `0y` prefix, not `0b` |
| `0xFFXX` | Hex mask | `X` = don't-care nibble |
| `10s` | 10 seconds | Time literal (also: `ms`, `us`, `ns`) |

### Expression Gotchas

| Mistake | Fix |
|---------|-----|
| Wrong operator precedence (13 levels) | Use parentheses to be explicit |
| Classic `:A:` `:O:` `:X:` operators | Valid — means AND/OR/XOR respectively |
| `{D:0x1000}` looks like a block | It's a braced constant (freezes address) |

### Macro Pitfalls

| Mistake | What Happens | Fix |
|---------|-------------|-----|
| Using undefined macro | Silent empty string | Check with `SYMBOL.EXIST.MACRO()` |
| `&x` vs `&&x` | `&x` = value; `&&x` = reference | Use `&&` for pass-by-reference |
| `"&name"` in string | Gets substituted | Use `CONV.CHAR()` to prevent |
| No typed variables | All macros are text substitution | Cast: `VAR.VALUE(&x)` for numeric |

### Common Command Mistakes

| Mistake | Fix |
|---------|-----|
| `Data.Set` without access class | Specify: `Data.Set D:0x1000 %Long 0xFF` |
| `Break.Set` on wrong address type | Use `P:` for program: `Break.Set P:main` |
| Forgetting `WAIT` after async cmd | Add `WAIT 1s` or poll `STATE.RUN()` |
| Path with spaces unquoted | Quote: `Data.LOAD.auto "my file.elf"` |
