# Isolated threads cannot carry arrays/structs as arguments or struct results (2026-11-16)

Status: open (workaround in place)

## Defect

`thread_spawn_with_args(data1, data2, worker)` (`src/lib/nogc_sync_mut/concurrent/thread.spl`)
only works when both data arguments are scalars. Measured with the interpreted
seed (`simple.exe run`, Windows, 2026-11-16):

| probe | result |
|---|---|
| args `(i64, i64)`, worker returns `[i64]` | `join()` = `Some([2, 5, 7])` (works) |
| args `([[u8]], i64)` or `([i64], i64)` | `join()` = `None` (the worker never produced a value) |
| arg `struct{[text], [[u8]], {text: i64}}` | `join()` = `None` |
| args `(i64, i64)`, worker returns a struct | `join()` = `Some(<invalid-heap:0x...>)` |
| `Channel.send(struct)` / `try_send([i64])` from a worker | `try_send` = false, `recv` hangs (> 600 s) |
| worker reads a module global `[[u8]]` set before spawn | works (`[1, 2, 8]`) |

Native build (Windows, 2026-11-16): `ThreadHandle.join()` is declared
`-> i64?`, so an `[i64]` result read through it segfaults or is lost. An
extern `rt_thread_join(handle) -> [i64]?` reads it correctly
(`len=3 v=7`). `elf_par.spl` uses the typed extern.

So no structured message can cross a thread boundary except a flat `[i64]`
returned through `join`, and inputs can only be shared through module globals.

## Impact

The internal ELF linker cannot parse objects in parallel: a parsed
`ElfObject` (a struct) cannot be returned from a worker. Relocation scan and
apply are parallel because their results encode as flat `[i64]`.

## Workaround

`src/compiler/70.backend/linker/elf/elf_par.spl`: the owner publishes an
immutable snapshot in module globals (admitted by one CAS gate), workers take
an index range `[lo, hi)` as scalar arguments and return a flat `[i64]`
through `join`, and the owner merges the results in range order.

## Fix wanted

Deep-copy (or move) array/struct arguments into the isolated worker, and
transfer struct/array results and channel messages the same way.
