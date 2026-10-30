# Core-C hosted stdin line provider missing

The Windows ordinary LLVM runner target at e01669c1bde compiled its selected
modules but failed final linking on `rt_read_stdin_line`. The narrow
`std.nogc_sync_mut.sffi.host_text` owner declares this symbol as tagged text;
the standalone core-C runtime did not provide it. No runner executable or
runner test result was produced by that failed build.

The Rust provider reads an unlimited UTF-8 line, preserves embedded NUL,
strips LF and an immediately preceding CR, returns empty text at EOF, and
returns NIL on read/decode error. Its mock interception belongs to the Rust
runtime; standalone core-C has no stdin mock owner. The raw-pointer
`rt_stdin_read_line` and fixed-4096-byte `rt_stdin_read_line_text` exports have
different contracts and cannot serve as ABI aliases. Pure-Simple file text
sessions have bounded codec/Result semantics and are not this hosted ABI.

The repair adds the missing tagged provider using a dynamically grown byte
buffer, existing UTF-8 validation and text allocation. Existing stdio binary
initialization on Windows preserves Ctrl-Z, CR and NUL. A stream lock spans
each complete line. Allocation failure returns NIL without a partial result.
Legacy helpers and the Simple extern declaration remain unchanged.

`scripts/check/check-core-stdin-line.py` compiles actual production runtime
owners and drives fresh raw stdin pipes. Its 19 cases cover newline/EOF,
multiple reads, long lines, UTF-8 including malformed input, embedded NUL,
Ctrl-Z, BOM preservation and a real closed-descriptor I/O error. All 19 cases
passed on Windows using LLVM-MinGW and the eight actual production owners.
The bounded run exited 0, quiescent, with peak RSS 151,220 KiB under a 2 GiB
tree cap (53 samples). The probe SHA256 is
`15ded306206bd5df212f50e34c7e7aed88400e394c3e35f66db1328da8373016`.
Evidence is retained under
`build/runner-goal-logs/core-stdin-line-capture-20261030-pathfix/` in the
isolated repair checkout. An earlier watcher setup failure ran no tests and
is not a provider failure. This is C-runtime ABI evidence. The actual
runner target must also link and execute with this provider before claiming
runner acceptance. No admitted compiler or runtime capsule is rewritten.
