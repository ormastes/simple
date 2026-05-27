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
| Simple hello | 451552 | 0.4 MB |
| Simple minimal TUI | 451552 | 0.4 MB |
| C hello | 14472 | 14.1 KB |
| C ncurses hello | 14472 | 14.1 KB |

## Simple Hello Sections

- text=421181, data=19848, bss=368, dec=441397
- .text: 04f8f0
- .rodata: 00b5e8
- .eh_frame: 007acc
- .gcc_except_table: 001aa0
- .data: 000a00
- .bss: 000100

## Simple Minimal TUI Sections

- text=421205, data=19848, bss=368, dec=441421
- .text: 04f8f8
- .rodata: 00b5f8
- .eh_frame: 007acc
- .gcc_except_table: 001aa0
- .data: 000a00
- .bss: 000100

## Anchor Strings

### Simple hello
- none

### Simple minimal TUI
- none

## Notes

- The generated TUI entry uses `app.ui.tui.standalone.run_standalone_tui`.
- The Simple artifacts are built on the explicit bootstrap-floor lane: `--runtime-bundle core-c-bootstrap`.
- This audit measures the bootstrap core floor, not the default `auto` lane once `simple-core` is available.
- The audit intentionally records anchor strings instead of claiming full transitive Rust crate closure proof.
- Set `MAX_HELLO_SIMPLE_BYTES` and/or `MAX_MINIMAL_TUI_BYTES` to turn the audit into a size-budget gate.
- Use `scripts/check-tui-standalone-closure.shs` alongside this report for the import-surface guard.
