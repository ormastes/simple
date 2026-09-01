# Pure-Simple Cranelift CLI corrupts lexer tokens

## Status

Open, release-blocking for self-hosted VHDL generation.

## Reproduction

Build the current full CLI with the fixed bootstrap seed, strict stub fallback,
Cranelift, entry closure, and either `one-binary` or `dynload`, then run:

```bash
SIMPLE_FRONTEND_DELEGATED=1 build/native_probe/simple_dynload \
  run scripts/fpga/riscv_linux_terminal_probe.spl --self-test
```

Both modes identify as `Simple v1.0.0-beta`, but the valid
`for arg in raw:` at line 25 is tokenized with `in` as `Ident`. Later tokens
are corrupted and execution ends with `runtime error: field access on nil
receiver` or SIGILL.

## Evidence

- Fixed-seed hash:
  `a5e9ddcf888a78d53cb54a4f67e1801a539aa215c20fb5393127661f669983bc`.
- One-binary: 1390 compiled, zero failed; focused runtime probe fails.
- Dynload: 1386 cached, 4 compiled, zero failed; identical probe failure.
- Essential-tools smoke fails its first `validate-json.spl` probe with unresolved
  `i64`, `get_cli_args`, and `json_parse_with_error`.
- Runtime-control symbols are real globals and are called from `main`:
  `rt_set_args`, `__simple_runtime_init`,
  `__simple_call_module_inits`, and `__simple_runtime_shutdown`.
- LLVM cannot substitute for this build: 95 current full-CLI modules require
  qualified-vtable/global-load support that the LLVM native-project backend
  explicitly rejects.

## Required fix

Isolate the first corrupted value between
`frontend__core__lexer__lex_init_with_path`,
`frontend__core__tokens__keyword_lookup`, and the Cranelift text/array lowering.
Add a focused native regression that tokenizes `for arg in raw:` and requires
`TOK_KW_FOR`, `TOK_IDENT`, `TOK_KW_IN`, `TOK_IDENT`, `TOK_COLON` before
rebuilding the full CLI. Do not deploy a version-only binary or fall back to
the Rust seed.
