# Unit range-cast / remainder checks: native execution blocked (2026-11-19)

Status: verification-pending (Lane 8, 2026-11-23: port_in, port_oor, big_accept and big_reject verified natively; div_zero builds but its executable segfaults (rc 139) before printing, see Lane 8).

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

## Lane 5: existing post-11-19 self-hosted CLI, native-build of the fixtures (2026-11-22, worktree rbnat4 @ 6caedc506bb)
Result: fixtures NOT run natively. Status stays verification-pending (no fixture built, so nothing verified).

Compiler search: `bin/release/**` does not exist; no `stage*` dir under any `C:/dev/wt/*/build/bootstrap` or `*/bootstrap` holds a binary newer than 11-19. Only candidate with `SPL-UNIT-005` in `strings`: `C:/dev/wt/ctorfix-20261121/build/nb/cli_main.exe` (114 MB, 2026-11-22 08:28, full pure-Simple CLI source `src/app/cli` built by the seed; `--version` = `Simple v1.0.0-rc.1`). Copied to `build/rbnat4/cli_main.exe` (untouched original). Every `bin/simple.exe` in the other worktrees is the tracked seed (0 hits). No bootstrap was attempted: the existing binary got further than any prior lane, and a fresh bootstrap would hit the same SCV/link stages.

Env: llvm-mingw UCRT first on PATH. Attempts, each `native-build ... -o build/rbnat4/out/port_oor.exe`:
1. `test/fixtures/unit_native/port_oor.spl`, default flags: ~8 min, then `SCV-E-ENTRY: entry absent from frozen inventory` / `SCV freeze has no admitted source inventory ... entry closure is empty (source snapshot unavailable)`. (The `publish-current-write-failed` error did NOT recur on this binary.)
2. Same with `SIMPLE_SCV_FREEZE_FALLBACK=1`, also with `--source test/fixtures/unit_native --entry <f> --entry-closure`: `SCV-W-FREEZE-FALLBACK`, then `SOURCE_ROOT_SELECTORS_MISSING` in phase load_sources. Cause in source: `native_build_closure_source_roots_v1` returns `Ok([])` when `_nb_scv_unfrozen_closure_v1` is set, and `native_source_root_paths_v1` (`driver_build/native_source_root_handoff.spl:8`) rejects empty selectors when a snapshot root is set. The fallback path is therefore unusable together with a snapshot root (new bug candidate).
3. Fixture copied into a scratch `src/app/rbnat_fx/` (uncommitted, removed) so the default roots cover it, no env: freeze OK, parse/HIR/MIR/optimize/codegen all succeed (`app.rbnat_fx.port_oor`, 1/1 module, ~40 s, rss 876 MiB), then phase=link hangs: no linker child process, no output, no `.exe`; killed by `timeout 1500` (25 min).
4. Same with `SIMPLE_LINKER=lld`: identical link hang, killed by `timeout 900`.

Exit codes / stdout / stderr of the fixtures: none exist (no executable produced). Build logs: `C:/dev/wt/rbnat4/build/rbnat4/out/port_oor.build{,2,3,4,5}.log` (untracked).

Remaining blockers, in order: (a) link phase of the pure-Simple native-build hangs on Windows before spawning any linker (same symptom as Lane 3's 1500 s `_LinkerWrapper/native_linking.spl` timeout under the cranelift seed build); (b) `SIMPLE_SCV_FREEZE_FALLBACK=1` yields empty root selectors; (c) entries outside `src/{app,lib,compiler,os,plugins}` are absent from the frozen inventory. Next: root-cause (a) (attach to the link phase / trace what native_linking.spl waits on), then rerun the five fixtures.

## Lane 6: native verification with the self-hosted CLI (2026-11-22, after #10894 / 7c1ee5d56b7)
Compiler: `C:/dev/wt/rbnat4/build/rbnat4/cli_main.exe` (sha256 prefix `b6eb1fefbe705621`, 114,562,560 B, Nov 22 09:16).
Env: `SIMPLE_LLVM_MINGW_ROOT=C:/Users/user/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64`, with its `bin` first on PATH.
Fixtures copied to scratch `src/app/rbnat_fx/` (uncommitted), because entries outside the default roots are absent from the frozen inventory (Lane 5 (c)).
Command: `timeout 2400 cli_main.exe native-build src/app/rbnat_fx/<case>.spl -o build/rbnat4/nv/<case>.exe`, then run the exe.
Warm-up: `hello` built in 14m46s cold (rc=0), printed `hello`, run rc=0. The link phase no longer hangs.

| case | build rc / wall | run rc | stdout / stderr | verdict |
|---|---|---|---|---|
| port_in | 0 / 3m05s | 0 | `in-range ok` | PASS (native) |
| port_oor | 0 / 2m52s | 1 | `in-range ok`; stderr `panic: SPL-UNIT-005: value <runtime value outside 1..65535> violates the constraint of unit `Port` (`1 <= self and self <= 65535`)`; `UNREACHED` not printed | PASS (native SPL-UNIT-005 guard) |
| big_accept | 1 / 1m36s | - | parse error 1:43 `unsupported constraint predicate for unit `Big`: `0 <= self and self <= 0xFFFF_FFFF_FFFF_FFF0`` | FAIL (native compile: the hex/underscore u64 bound is not accepted by the constraint predicate parser) |
| big_reject | 1 / 1m34s | - | same parse error as big_accept | FAIL (same cause) |
| div_zero | 1 / 1m42s | - | MIR: `unresolved method call: operator overload for struct ...::Dist (no matching __add__/.../__div__ impl)` at div_zero.spl:4:5 | FAIL (native MIR: `/` is not lowered on a plain `unit Dist: i64`) |

Logs: `C:/dev/wt/rbnat4/build/rbnat4/nv/<case>.build.log` (untracked).
Status stays verification-pending: the u64 bound and div0 (SPL-UNIT-002) paths are still not verified natively.
Handoff: (1) the unit constraint predicate parser rejects hex/underscore literals (`0xFFFF_FFFF_FFFF_FFF0`); (2) native MIR does not lower arithmetic on a unit with no range.

## Lane 7: source fixes for the Lane 6 compile failures (2026-11-23, work/nu1-20261123)
Neither failure was already fixed in release/1.0.0 source (checked at 9526382f4f5).
- Hex/underscore bound: `unit_constraint.spl` tokenizer, `unit_constraint_parse_number` and `uc_bound_int` now accept `0x`/`0b`/`0o` literals with `_`. New `unit_radix_bound_bits` keeps a hex bound's 64-bit pattern; MIR `unit_range_bound_i64` uses it, so `0xFFFF_FFFF_FFFF_FFF0` becomes the u64 constant instead of `parse_i64`'s `-1`.
- `/` on a plain `unit Dist: i64`: `emit_unit_div_remainder_check` now panics with `SPL-UNIT-002: unit division by zero` on a zero divisor (it used to skip to the trapping Div) and returns the i64 quotient of the payload words. Same-unit division returns that quotient, so the record-operator path no longer reports a missing `__div__`.
- Specs: `unit_constraint_decl_spec.spl` (4 new cases, 29/29) and `unit_div_remainder_native_spec.spl` (2 new cases, 7/7; the new cases were red before the fix). `unit_range_cast_native_spec.spl` stays 14/14.
- Limit: the interpreter evaluates predicates in f64, so it cannot tell `0xFFFF_FFFF_FFFF_FFFF` from the bound `0xFFFF_FFFF_FFFF_FFF0`. The native check compares integers and is exact.
Native re-verification still needed: rebuild the self-hosted CLI from a tree containing this change, then re-run Lane 6 for big_accept, big_reject and div_zero.

## Lane 8: native re-verification after #10894 / #10901 / #10909 (2026-11-23, worktree nv2)
Tree: release/1.0.0 at `d83c3a98dc8`. It contains `7c1ee5d56b7` (#10894), `3b3c0cc4f59` (#10901) and `cf87604ac86` (#10909).
Compiler: `C:/dev/wt/nv2/build/nv2/cli_main.exe`, 116,882,432 B, sha256 `ea78bedd0911fd97f163dd8f353dd3c6c65e5866fcb99a308a8c5167d42122a2` (`--version` = `Simple v1.0.0-rc.1`).
How it was built: Rust seed `C:/dev/simple/bin/simple.exe` (sha256 prefix `d1e16e3da724b4d9`, build-commit `f3e12b05d39`), command:
`SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1 seed native-build --source src/compositions/kernel_llvm_cranelift --source src/compiler --source src/app --source src/lib --source src/os --source src/plugins --entry-closure --entry src/app/cli/main.spl -o build/nv2/cli_main.exe --cache-dir build/nv2/cache --timeout 3600 --threads 48`,
with `CC`/`CXX` set to llvm-mingw `clang.exe`/`clang++.exe`. 4,125 files, 31m00s, BUILD_RC=0.
Build notes:
- Without the `kernel_llvm_cranelift` composition root, the binary links but every command fails with `PLUG-E-K1-POLICY`.
- With no `CC` set, this seed links with `C:\Program Files\LLVM` clang 23 and fails on a missing `libclang_rt.builtins.a`.
- `test_db_compat.spl:394` needed a build-only workaround, which was not committed. See `seed_native_build_per_file_compile_minutes_windows_2026-11-23.md`.
Fixtures were copied to scratch `src/app/rbnat_fx/` (deleted afterwards), as in Lane 6. Fixture env: `SIMPLE_LLVM_MINGW_ROOT=C:/Users/user/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64`, with its `bin` first on PATH.
Command: `timeout 2400 cli_main.exe native-build src/app/rbnat_fx/<case>.spl -o build/nv2/nv/<case>.exe`, then run the exe.

| case | command | build rc / wall | run rc | stdout / stderr | compiler sha256 | verdict |
|---|---|---|---|---|---|---|
| port_in | `cli_main.exe native-build src/app/rbnat_fx/port_in.spl -o build/nv2/nv/port_in.exe; ./port_in.exe` | 0 / 6m59s | 0 | `in-range ok` | `ea78bedd…22a2` | PASS |
| port_oor | same, `port_oor` | 0 / 7m05s | 1 | `in-range ok`; stderr `panic: SPL-UNIT-005: value 70000 violates the constraint of unit `Port` (`1 <= self and self <= 65535`; range 1..65535)`; no `UNREACHED` | `ea78bedd…22a2` | PASS |
| big_accept | same, `big_accept` | 0 / 6m57s | 0 | `0x8000.. accepted` | `ea78bedd…22a2` | PASS (hex/underscore u64 bound now accepted, #10909) |
| big_reject | same, `big_reject` | 0 / 7m01s | 1 | `0x8000.. accepted`; stderr `panic: SPL-UNIT-005: value 18446744073709551615 violates the constraint of unit `Big` (`0 <= self and self <= 0xFFFF_FFFF_FFFF_FFF0`; range 0..0xFFFF_FFFF_FFFF_FFF0)`; no `UNREACHED` | `ea78bedd…22a2` | PASS |
| div_zero | same, `div_zero` | 0 / 7m03s | 139 (SIGSEGV, reproduced twice) | stdout and stderr empty: neither `10/5 ok` nor `SPL-UNIT-002` | `ea78bedd…22a2` | FAIL (native run: segfault before the first `print`) |

The five builds ran in parallel. Logs and executables are in `C:/dev/wt/nv2/build/nv2/nv/` (untracked).
Result: the compile failures from Lane 6 are gone. The u64 hex bound is verified natively. The `/` lowering now compiles, but the div_zero executable crashes even on the non-zero `10 / 5` call, so SPL-UNIT-002 is not verified natively.
Handoff: debug `div_zero.exe` (the `ratio(a: Dist, b: Dist) -> i64: a / b` path from `emit_unit_div_remainder_check`). The crash happens before the first `print`.
