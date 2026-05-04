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
| Simple hello | 410736 | 0.4 MB |
| Simple minimal TUI | 410736 | 0.4 MB |
| C hello | 14472 | 14.1 KB |
| C ncurses hello | 14472 | 14.1 KB |

## Simple Hello Sections

- text=381221, data=18896, bss=400, dec=400517
- .text: 046d68
- .rodata: 00c580
- .eh_frame: 006534
- .gcc_except_table: 001360
- .data: 000a90
- .bss: 000120

## Simple Minimal TUI Sections

- text=381837, data=18960, bss=400, dec=401197
- .text: 046f18
- .rodata: 00c5d8
- .eh_frame: 006584
- .gcc_except_table: 001360
- .data: 000a90
- .bss: 000120

## Anchor Strings

### Simple hello
- sha1: 1
- sha256: 1

### Simple minimal TUI
- sha1: 1
- sha256: 1

## Notes

- The generated TUI entry uses `app.ui.tui.standalone.run_standalone_tui`.
- The Simple artifacts are built on the explicit narrow native lane: `--runtime-bundle core-c`.
- The audit intentionally records anchor strings instead of claiming full transitive Rust crate closure proof.
- Set `MAX_HELLO_SIMPLE_BYTES` and/or `MAX_MINIMAL_TUI_BYTES` to turn the audit into a size-budget gate.
- Use `scripts/check-tui-standalone-closure.shs` alongside this report for the import-surface guard.
