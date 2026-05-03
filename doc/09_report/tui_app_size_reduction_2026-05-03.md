# TUI App Size Reduction Verification

Date: 2026-05-03

## Build Inputs

- Simple hello: `examples/01_getting_started/hello_native.spl`
- Simple minimal TUI: generated standalone entry -> `examples/ui/minimal.ui.sdn`
- C hello: `build/size_audit/hello.c`
- C ncurses hello: `build/size_audit/hello_ncurses.c`

## Byte Sizes

| Artifact | Bytes | Approx |
|---|---:|---:|
| Simple hello | 423024 | 0.4 MB |
| Simple minimal TUI | 427120 | 0.4 MB |
| C hello | 14472 | 14.1 KB |
| C ncurses hello | 14472 | 14.1 KB |

## Simple Hello Sections

- text=395588, data=19208, bss=400, dec=415196
- .text: 047f38
- .rodata: 00c4d0
- .data: 000a90
- .bss: 000120

## Simple Minimal TUI Sections

- text=396456, data=19272, bss=400, dec=416128
- .text: 0480e8
- .rodata: 00c528
- .data: 000a90
- .bss: 000120

## Anchor Strings

### Simple hello
- sha256: 1

### Simple minimal TUI
- sha256: 1

## Notes

- The generated TUI entry uses `app.ui.tui.standalone.run_standalone_tui`.
- The audit intentionally records anchor strings instead of claiming full transitive Rust crate closure proof.
- Use `scripts/check-tui-standalone-closure.shs` alongside this report for the import-surface guard.
