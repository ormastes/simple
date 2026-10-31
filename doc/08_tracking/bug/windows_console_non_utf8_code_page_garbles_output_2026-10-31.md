# Windows console on a non-UTF-8 code page garbles Simple output

**Status:** open. **Found:** 2026-10-31, reviewing the caret/cmux landing branch.

## Symptom

Output written to a real console whose output code page is not 65001 is decoded
in that code page. Measured on the seed with a freshly allocated console, a child
printing `é界` through `sosix_print_raw` (line A) and `print` (line B), read back
with `ReadConsoleOutputCharacterW`:

| console output CP | A | B |
|---|---|---|
| 437 | `├⌐τòî` | `├⌐τòî` |
| 65001 | `é界` | `é界` |

Pipes are unaffected: `console_output_spec.spl` compares captured stdout byte for
byte. No `SetConsoleOutputCP` exists in `src/runtime` or the seed driver.

## Why it was not fixed at seed startup

`SetConsoleOutputCP(65001)` in the driver is small but not clearly correct:

- The code page belongs to the console, not the process, so it outlives the seed
  and changes how the parent shell's later legacy tools are decoded.
- It cannot be restored reliably. `std::process::exit` on Windows calls
  `ExitProcess`, which does not run an executable's CRT `atexit` handlers, and a
  killed process runs nothing.
- Children sharing the console that write in the OEM code page garble instead
  while the seed runs.
- It covers the seed only; native binaries would still need their own fix.

## Direction

Convert at the write instead of changing console state: when a standard-stream
descriptor is a console (`GetConsoleMode` succeeds), write through
`WriteConsoleW`, as Rust's `std::io::Stdout` already does, in both the
interpreter and native runtime paths, keeping raw bytes for pipes and files.
Non-UTF-8 byte sequences and writes that split a character need a defined policy.
