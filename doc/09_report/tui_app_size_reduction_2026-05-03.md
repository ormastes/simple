# TUI App Size Reduction Verification

Date: 2026-05-27

## Build Inputs

- Simple hello: `examples/01_getting_started/hello_native.spl`
- Simple minimal TUI: generated standalone entry -> `examples/ui/minimal.ui.sdn`
- C hello: `build/size_audit/hello.c`
- C ncurses hello: `build/size_audit/hello_ncurses.c`

## Byte Sizes

| Artifact | Bytes | Approx |
|---|---:|---:|
| Simple hello | 26864 | 0.0 MB |
| Simple minimal TUI | 26864 | 0.0 MB |
| C hello | 14472 | 14.1 KB |
| C ncurses hello | 14472 | 14.1 KB |

## Simple Hello Sections

- text=18669, data=664, bss=168, dec=19501
- .text: 002b35
- .rodata: 000e29
- .eh_frame: 00072c
- .bss: 0000a8

## Simple Minimal TUI Sections

- text=18864, data=664, bss=168, dec=19696
- .text: 002be8
- .rodata: 000e39
- .eh_frame: 00072c
- .bss: 0000a8

## Anchor Strings

### Simple hello
- none

### Simple minimal TUI
- none

## Notes

- The generated TUI entry uses the narrow `app.ui.tui.screen` ANSI lane.
- The Simple artifacts are built on the explicit bootstrap-floor lane: `--runtime-bundle core-c-bootstrap`.
- This audit measures the bootstrap core floor, not the default `auto` lane once `simple-core` is available.
- The audit intentionally records anchor strings instead of claiming full transitive Rust crate closure proof.
- Set `MAX_HELLO_SIMPLE_BYTES` and/or `MAX_MINIMAL_TUI_BYTES` to turn the audit into a size-budget gate.
- Use `scripts/check/check-tui-standalone-closure.shs` alongside this report for the import-surface guard.
