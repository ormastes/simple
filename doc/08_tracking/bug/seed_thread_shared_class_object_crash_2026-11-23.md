# Bug: seed interpreter crashes when worker threads read a shared class object (2026-11-23)

Status: open. Severity: P0 (it blocks the RB-LOAD-02 multithreaded hot-swap stress spec).

## Symptom
`C:/dev/simple/bin/simple.exe test <spec>` (Windows, Rust seed) reports
`outcome=ERROR ... reason=child-died-by-signal` with `executed=0`. This happens
as soon as `thread_spawn_with_args` workers call methods on a `HotSwapSlot`
class instance owned by the main thread. It happens even when the access is
read-only.

## Discrimination (all on the same seed, same host)
| variant | workers touch the slot? | swaps | verdict |
|---|---|---|---|
| `rt_black_box_concurrent_identity_spec` (shares only `AtomicI64` handles) | no | n/a | OK 2/2 |
| stress, 4 readers x 2000 reads, 200 swaps + reclaims | yes (module `var`) | 200 | died by signal |
| control, 4 readers x 50 reads | yes (module `var`) | 0 | died by signal |
| control, worker body stripped to atomics only | no | 0 | OK 1/1 |
| control, slot passed as a thread argument instead of a global | yes (arg) | 0 | died by signal |

The crash needs no writer, so it is not the hot-swap protocol. A class object
reachable from more than one seed interpreter thread is enough to crash.

## Hot-swap side (fixed in the same change)
The OS-thread run could not execute. Review of the reader path still found a
real writer-vs-reader defect. Readers scanned a growable `images` array while
the writer `push`ed onto it (a reallocation race) and wrote `image` fields on
unpinned entries. `hot_swap_pin.spl` now uses a fixed-capacity table that is
allocated once. Readers index it by `generation % capacity`, pin by CAS, and
then confirm the generation. They never scan. A pinned entry is never reused
(`SMF-E-HOTSWAP-FULL`). The single-thread wrap spec in
`test/01_unit/compiler/loader/hot_swap_image_spec.spl` pins this.

## Next
- Fix the seed runtime so shared class instances are safe to read across
  threads, or run the stress spec on a native pure-Simple binary.
- Then land `test/01_unit/compiler/loader/hot_swap_stress_spec.spl`: N reader
  threads pin and read while the main thread swaps and reclaims. It asserts a
  reader count >= 1 and a non-empty image while pinned, and zero violations.
  The source is in the hs3 PR description.
