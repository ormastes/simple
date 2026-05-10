# TUI App Size Reduction Verification

Date: 2026-05-04

## Build Inputs

- Simple hello: `examples/01_getting_started/hello_native.spl`
- Simple minimal TUI: generated standalone entry -> `examples/ui/minimal.ui.sdn`
- C hello: `build/size_audit/hello.c`
- C ncurses hello: `build/size_audit/hello_ncurses.c`

## Byte Sizes

| Artifact | Bytes | Approx |
|---|---:|---:|
| Simple hello | 394200 | 0.4 MB |
| Simple minimal TUI | 394200 | 0.4 MB |
| C hello | 14472 | 14.1 KB |
| C ncurses hello | 14472 | 14.1 KB |

## Simple Hello Sections

- text=365905, data=17040, bss=368, dec=383313
- .text: 0457c8
- .rodata: 00a2f8
- .eh_frame: 006274
- .gcc_except_table: 00132c
- .data: 0009f8
- .bss: 000100

## Simple Minimal TUI Sections

- text=367121, data=17104, bss=368, dec=384593
- .text: 045978
- .rodata: 00a5a8
- .eh_frame: 0062c4
- .gcc_except_table: 00132c
- .data: 0009f8
- .bss: 000100

## Anchor Strings

### Simple hello
- none

### Simple minimal TUI
- none

## Notes

- The generated TUI entry uses `app.ui.tui.standalone.run_standalone_tui`.
- The Simple artifacts are built on the explicit narrow native lane: `--runtime-bundle core-c`.
- The audit intentionally records anchor strings instead of claiming full transitive Rust crate closure proof.
- Set `MAX_HELLO_SIMPLE_BYTES` and/or `MAX_MINIMAL_TUI_BYTES` to turn the audit into a size-budget gate.
- Use `scripts/check-tui-standalone-closure.shs` alongside this report for the import-surface guard.
