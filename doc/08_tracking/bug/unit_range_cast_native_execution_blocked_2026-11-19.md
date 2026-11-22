# Unit range-cast / remainder checks: native execution blocked (2026-11-19)

Status: verification-pending. Native machine-code verification NOT achieved.

Fixtures: `test/fixtures/unit_native/{port_oor,port_in,big_reject,big_accept,div_zero}.spl`.

## Lane 1: Rust seed native-build (works, but does not exercise the pure-Simple MIR checks)
Env: llvm-mingw UCRT on PATH (`~/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin`), `SIMPLE_NATIVE_BUILD_RUST=1`.
(`CC=clang-cl` compiles but fails to link: missing libclang_rt.builtins.a / liblibcmt.a / liboldnames.a.)

    SIMPLE_NATIVE_BUILD_RUST=1 C:/dev/simple/bin/simple.exe native-build test/fixtures/unit_native/<case>.spl -o build_rbnat2/<case>.exe

Observed (all five link, rc=0):

| case | exit | stdout | stderr |
|---|---|---|---|
| port_oor (`mk(8080)`, `mk(70000)`) | 0 | `in-range ok` / `UNREACHED` | empty |
| port_in (`mk(8080)`) | 0 | `in-range ok` | empty |
| big_reject (`mk(0x8000_0000_0000_0000)`, `mk(0xFFFF_FFFF_FFFF_FFFF)`) | 0 | `0x8000.. accepted` / `UNREACHED` | empty |
| big_accept (`mk(0x8000_0000_0000_0000)`) | 0 | `0x8000.. accepted` | empty |
| div_zero (`10/5` then `10/0` on `unit Dist: i64`) | 132 (SIGILL) | `10/5 ok` | empty |

The seed's Rust codegen emits no SPL-UNIT-005 / SPL-UNIT-002 guard: out-of-range casts pass, the u64 bound is not enforced, and `x / 0` hardware-traps. This is the seed lowering, not the pure-Simple MIR that the MIR specs cover, so it neither confirms nor refutes the pure-Simple checks. The seed does not implement unit range checks natively (separate gap; the interpreter path does).

## Lane 2: pure-Simple native-build via the seed interpreter (no env var)
    timeout 900 C:/dev/simple/bin/simple.exe native-build test/fixtures/unit_native/port_oor.spl -o build_rbnat2/port_oor_ps.exe
Result: no artifact; killed by timeout, rc=124 after 900 s, last line `workarounds: incomplete coverage; run simple check-dbs --fullscan bugs`, ~8.5k lines of visibility warnings. Matches the known "bare seed native-build interprets native_build_main.spl and never finishes".

## Conclusion
Blocked: no deployed self-hosted native compiler on this host. Re-run the five fixtures with a pure-Simple compiled `simple native-build` once deployed; expected: port_oor panics with SPL-UNIT-005 naming Port and 1..=65535; big_reject rejects 0xFFFF_FFFF_FFFF_FFFF and accepts 0x8000_0000_0000_0000; div_zero exits via SPL-UNIT-002 not SIGILL.

## Lane 3: pure-Simple compiler search and rebuild (2026-11-19, worktree rbnat3 @ aff531f811c)
Result: fixtures NOT run natively. Status stays verification-pending.

Candidates found (none usable as-is):
- `C:/dev/simple/bin/simple.exe` (Nov 19 19:22) and `C:/dev/wt/rbnative/bin/simple.exe` (Nov 19 19:45): Rust seed (prints the seed WARNING banner). The newest seed has no `llvm` feature (`native backend 'llvm' is not available in this build`).
- `build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected` (Oct 9): pure-Simple, rejected stage2; `native-build hello` dies with `str.clear was called on a receiver that is not text`. Predates unit range lowering.
- Prior-session `p3mir/stage2{,_prev,c,d,e}.exe` (Nov 16-19 13:06) built by the seed: `--version` ok, but `SPL-UNIT-005` string is absent from `stage2d`/`stage2e`, i.e. older than #10468/#10469 (stage2e 13:06 < fix b54208a1908 20:07). Ruled out. `stage2e` hello also refused by the worker memory budget on this host (free 14.9 GB vs 58.7 GB needed; WSL holds ~27 GB).
- No `bootstrap/stage3` binary links on this host (known phase-3 0-object issue; stage2b rebuild with a pure-Simple builder hit a 4h limit at 16 objects).

Fresh stage2 from release tip (diagnostic, `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=6442450944`, worker KB 3145728, not an admitted/deployed compiler):
- seed_llvm.exe (Nov 17 seed) `native-build --backend llvm --target x86_64-pc-windows-gnu --entry src/app/cli/bootstrap_main.spl`: first attempt 1587 compiled, 1 failed: `src/lib/common/text_bytes.spl: hir: cannot infer field type ... struct 'ANY' field 'value'` (unit `Capacity.value` unresolved by that older seed; introduced by 0372477f52e).
- With a throwaway local workaround in text_bytes.spl (params `Capacity`/`Length` -> `i64`, `.value` dropped; reverted, not committed) the same command built `stage2.exe` (26.4 MB, ~5 min, `SPL-UNIT-005` string present, `--version` = `simple-bootstrap 1.0.0-rc.1`).
- newest seed with `--backend cranelift`: one worker (`70.backend/linker/_LinkerWrapper/native_linking.spl`) hit the 1500 s timeout, 1514 files cascaded NOT_ATTEMPTED.

Blocker: the fresh stage2 cannot native-build even hello world: `SCV-E-ADMISSION: observed-event-apply:inventory-publication-failed:publish-current-write-failed` (reproduced 3x: default flags; with `SIMPLE_SCV_INVENTORY_COLD_INIT/FREEZE_FALLBACK/NATIVE_INCREMENTAL/CACHE_SCOPE/PROJECT_ROOT` as in the p3mir recipe; with `--source build/rbn --entry-closure`). Source is inside the git checkout root; the write failure message carries no path. No fixture was built or run natively.

Next: root-cause `publish-current-write-failed` (SCV inventory publication under a git worktree), and/or rebuild the llvm seed so text_bytes.spl compiles without the workaround; then re-run the five fixtures with the fresh stage2.

## Lane 4: `publish-current-write-failed` root cause (2026-11-22, branch work/scvpub-20261119)
Result: fixtures still NOT run natively. Status stays verification-pending.

Root cause of `SCV-E-ADMISSION: observed-event-apply:inventory-publication-failed:publish-current-write-failed`:
it is not a bug in the tree. The Lane 3 stage2 (`rbn3/stage2.exe`) was built with an incomplete local
text_bytes workaround. That workaround changed `text_byte_buffer`/`text_byte_extraction_checked` to take
`i64`, but left the `Capacity(value: ...)`/`Length(value: ...)` call sites in place. In that binary the
UTF-8 encoder (`file_atomic_write` -> `file_atomic_write_encoded_text` -> `external_byte_buffer` ->
`text_byte_buffer`) therefore fails. Every encoded `file_atomic_write` returns false, so the CURRENT
pointer write fails. The generation blobs still publish, because they go through
`file_publish_noreplace_raw`, which does not encode.
Evidence:
- On Nov 19, CURRENT was moved away and the run repeated: a new generation blob was written in the same
  second, but CURRENT was still not written. Replace-over-existing is ruled out.
- A stage2 built with the workaround applied to all 14 call sites (`s4/stage2.exe`, local only, never
  committed) published CURRENT fine in a fresh worktree on a disk that was 100% full.
- In the same worktree minutes later, `rbn3/stage2.exe` panics with
  `panic: external text at byte -1: boxed text byte extraction failed`.

Committed change (diagnostic only, not a Windows write fix): the inventory publication reasons now end
with `path=<target>`. Spec: `test/01_unit/lib/scv/compile_source_inventory_lockless_publish_spec.spl`
("names the CURRENT path when the pointer write fails"). It failed before the change (6/7) and passes
after it (7/7, also on the rebased tip 6caedc506bb).

Native runs with `s4/stage2.exe` (seed_llvm build of the pre-rebase tree with the local workaround,
not admitted):
- `native-build test/fixtures/unit_native/port_in.spl`: SCV admission, HIR and MIR succeed
  (`[mir-shard] link modules=1 objects=1`). The link phase then hangs until `timeout 1200` (worker
  exit 143). No artifact.
- A second attempt hung before link (`timeout 150`, rc=124).
- Host C: was 100% full (2.5 GB free); cache writes were refused (`[cache-admission] publish refused`).
  A fresh stage2 rebuild from the current release tip was not attempted for lack of disk.

Next: on a host with free disk, rebuild stage2 from the current release tip. That tip carries the linker
and driver fixes that landed after Nov 19. Then re-run the five fixtures. If the link still hangs, check
whether `native_linking.spl` spawns clang/lld at all.
