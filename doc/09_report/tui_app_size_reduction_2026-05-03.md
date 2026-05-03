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
| Simple hello | 423016 | 0.4 MB |
| Simple minimal TUI | 427112 | 0.4 MB |
| C hello | 14472 | 14.1 KB |
| C ncurses hello | 14472 | 14.1 KB |

## Simple Hello Sections

- text=396556, data=19232, bss=400, dec=416188
- .text: 047f98
- .rodata: 00c820
- .data: 000a88
- .bss: 000120

## Simple Minimal TUI Sections

- text=397424, data=19296, bss=400, dec=417120
- .text: 048148
- .rodata: 00c878
- .data: 000a88
- .bss: 000120

## Anchor Strings

### Simple hello
- regex: 6
- sha1: 1
- sha256: 1

### Simple minimal TUI
- regex: 6
- sha1: 1
- sha256: 1

## Notes

- The generated TUI entry uses `app.ui.tui.standalone.run_standalone_tui`.
- The generated TUI and hello audit lane now build with `--runtime-bundle runtime` and source roots `src/lib` + `src/app`, intentionally excluding `src/compiler`.
- The audit intentionally records anchor strings instead of claiming full transitive Rust crate closure proof.
- Use `scripts/check-tui-standalone-closure.shs` alongside this report for the import-surface guard.
- The prior 14 MB plateau was traced to the audited caller selecting the broad `libsimple_native_all.a` lane by passing `--source src/compiler`, which made `native-build` classify the build as compiler-like.
