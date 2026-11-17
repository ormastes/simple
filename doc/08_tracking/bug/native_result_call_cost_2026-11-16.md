# Native codegen: a Result-returning call costs ~5 us and leaks per call

- Date: 2026-11-16
- Status: open (codegen, not fixed). Linker workaround round 3 (2026-11-17): verification-pending.
- Area: native codegen of `Result<T, E>` returns, `.unwrap()` and `?`
- Found by: `internal_elf_linker_perf_200obj_2026-11-16.md` (round 2)

## Repro

120k calls, Windows x86_64 native (`SIMPLE_NATIVE_BUILD_RUST=1 native-build`):

| shape | total ms | hwm growth |
|---|---|---|
| `fn f(x: i64) -> i64` | 1 | 0 |
| `fn f(x: i64) -> Result<i64, text>` then `.unwrap()` | 572 | ~8 MB (~66 B/call) |
| caller `-> Result` doing `f(x)?` on the same `f` | 1070 | ~21 MB (~175 B/call) |

So one Result return costs about 4.8 us and a `?` about 9 us, 500-1000x a
plain call, and neither frees its Result box. The same body inline costs
about 0.03 us.

Probe source (one file):

```
fn plain(x: i64) -> i64: x + 1
fn res(x: i64) -> Result<i64, text>: Ok(x + 1)
fn via_q(x: i64) -> Result<i64, text>: Ok(res(x)? + 1)
```

Time 120k calls of each with `time_now_unix_micros` and read hwm from
`SIMPLE_ELF_LINK_TRACE`-style RSS sampling.

## Impact

In the internal ELF linker, the per-relocation helpers `elf_symref`,
`elf_placed_offset`, `elf_ref_addr`, `elf_ref_value` and `elf_in_vaddr`
each returned Result. They cost about 4 s of a 7.9 s link of 120k relocations.

## Workaround in tree

`elf_static_link.spl`: `elf_symref` returns `ElfScanRef` with kind
`SYMREF_ERR` and the message in `key`; `elf_ref_value_fast` /
`elf_in_vaddr_fast` return `ELF_ADDR_SLOW` and the caller falls back to the
Result resolver only for rare cases. Since 2026-11-17 the apply loops use
`ElfSealedOperationsV1.relocate_fast` (builtin operations only; `[]` means
fall back to `relocate`), and symtab uses `elf_entry_addr_fast`
(apply 1.47 s -> 0.68 s, symtab 1.55 s -> 0.97 s; linker fixes are
verification-pending, this codegen bug stays open). Tagged
`# workaround: doc/08_tracking/bug/native_result_call_cost_2026-11-16.md`.

## Fix direction

Return small `Result<scalar, text>` by value (tag + payload in registers)
and free the error/ok box on `unwrap`/`?`. Remove the workaround when the
repro shows plain-call cost.
