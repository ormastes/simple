# Candidate mis-passes length operand of three-argument mixed text externs (2026-10-22)

**Status:** OPEN — worked around by two-argument open twins (see
`stage2_sanity_scv_snapshot_entry_zero_sources_2026-10-22.md`); the codegen
defect itself is unfixed.
**Impact:** any seed-produced (stage-2+) Simple binary mis-passes the second
operand of a three-argument extern whose first parameter is a `text`
expanded to (ptr, len) — observed as `path_len = -1` (0xFFFFFFFFFFFFFFFF)
at the Rust ABI boundary.

## Evidence

During the 2026-10-22 Windows Stage-2 sanity investigation (lane attempts
14-20), an env-gated diagnostic in the Rust `rt_io_file_open`
(`src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs`) printed:

```
[rt_io_file_open-rust-diag] invalid-utf8 len=18446744073709551615 bytes=[...
```

`len = u64::MAX = (u64)-1`: the `path_len` operand arrived as -1. The
Simple call site was the raw three-argument form
`rt_io_file_open(address, count, mode)` in
`src/lib/nogc_sync_mut/sffi/fs.spl`, where `count` came from
`rt_string_len(path)` (a one-argument extern whose result is used
immediately and correctly elsewhere). Two-argument (ptr, len) text externs
in the same binary pass correctly — `rt_io_file_exists` admitted the same
paths that `rt_io_file_open` failed on, and the same candidate's
scv_prime step compiled the working-tree entry (its reads route through
different, working entry points).

Conclusion: the seed-produced candidate's codegen sets up the operand
registers of three-argument mixed (ptr, len, scalar) text externs
incorrectly — the scalar (third) argument setup clobbers the length
(second) operand. This is the same defect class as the historical
`rt_file_open` note in `src/runtime/runtime_native.c` (~line 14524):
"RuntimeFuncSpec declares 4 I64 params, but the real call ... only ever
sets up 3 registers".

## Observable symptoms

- Every mode-0/1/3 `io_file_open` in the candidate returns -1 regardless
  of the path value or its provenance (Simple-created or C-created).
- `FileTextSession`-based reads (`file_read_nullable`) return nil, which
  surfaces downstream as the load_sources zero-source gate.
- One-argument text/tagged externs and two-argument (ptr, len) text
  externs work.

## Workaround (landed with the Stage-2 fix)

Two-argument open twins `rt_io_file_open_read/write/append` in both
runtimes (C `runtime_native.c` and Rust `io_file.rs`), with
`sffi/fs.spl` dispatching by mode. Mode 2 (ReadWrite) still routes through
the three-argument form and remains broken on seed-produced candidates.

## Proper fix (not done)

Find the seed compiler's extern-call lowering for mixed text+scalar
signatures (the register/operand setup for the expanded (ptr, len) pair
followed by additional scalar operands) and fix the operand assignment so
the length word survives the third-argument setup. Reproduce minimally: a
native-compiled binary calling a 3-arg (text, i64) extern with a known
string, asserting the callee receives the correct length.
