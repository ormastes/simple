# Windows bootstrap: did switching to llvm-mingw (UCRT) cause today's compiler problems?

**Date:** 2026-11-05. **Scope:** read-only analysis of the Windows bootstrap chain used by phase 3/4
(`C:/dev/p3new`), the tracked seed, git history and the bug records. No code was changed.

**Verdict: NOT toolchain-caused for the compiler-logic classes (stage2 miscompiles, E-RTI-006,
`native_trait_owner_for_type` AV, the wild-RIP-after-"rejected invalid array handle", the shard
memory admission). PARTLY toolchain-caused for exactly two operational classes: the stage2 exit 127
(`libLLVM-23.dll` PATH clash, a packaging defect of the llvm-mingw lane) and, historically, a
stage2 RSS runaway attributed to the CLANG64 `libLLVM-23.dll` build (fixed 2026-10-23).**
MinGW-vs-MSVC did not change calling convention, mangling, struct return, or source selection
(details in sections 3 to 6). Switching the whole chain to the MSVC lane would not remove the
compiler-logic bugs and would reintroduce the problems that made the lane switch happen
(section 7).

## 1. Current problems (2026-11-05) with toolchain verdict and status

| Problem | Toolchain verdict | Status / owner |
|---|---|---|
| Phase 3: `s3_fable43`/`44` pass the gates; test runner crashes with `native_trait_owner_for_type+0x202e` AV (addr 0, after `rejected invalid array handle`) | **Not MinGW** — by-value copy of an Option transport word in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (~6110/~6120); a 64-bit word, not an aggregate, so Win64 aggregate passing cannot be involved | Fixed by PR #6933 (merged 2026-11-05, `3eaaed755c6`, spec `test/01_unit/compiler/mir/cast_convert_target_rebuild_spec.spl` 3/3); goes into `s3_fable45` (drvfix7/8, `C:/dev/p3new/cgprobe/fable_drvfix7.ps1`) |
| drvfix builds slow or killed by MIR shard memory admission (`mir-shard.<producer>.peak_kib` = 51 GB from a previous run; 4 shards x 30 GB budget) | **Not MinGW** — admission is pure-Simple driver policy (`src/compiler/80.driver`, `[mir-shard]` pool); `fable_milestones.md:398,416` | Open; phase-3 lead; recent related landings `9cbe9c290a1` (clamp shard fan-out), `7f279dbf310` (process-parallel codegen pool) |
| Phase 4 paused on E-RTI-006 nondeterminism (`two rows for callee main`, row text = build-log garbage) on the driver route | **Not MinGW** — class-field bracket read of a dangling text handle in `src/compiler/20.hir/return_type_interface_v1.spl:523-`; identical on gate route 3/3 PASS vs driver route 1/2, i.e. a data-race/lifetime bug in .spl, not ABI | Fixed by PR #6921 (merged `1746a8ecbed`; `.get()`/if-val + identical re-registration short-circuit); in `s3_fable45` |
| stage2 Option-word / by-value-struct miscompile family (bug tags `stage2_struct_param_deep_copy_packed_span_2026-11-03`, `stage2_if_val_struct_option_binding_as_int_wide_2026-11-03`, `stage2_local_symbol_index_bucket_tagged_id_2026-11-03` from `fable_milestones.md`/`LINK_NOTES.md`, records not yet on release/1.0.0; landed records `stage2_try_unwrap_text_typed_as_i64_2026-11-02`, `stage2_mir_field_type_garbage_carrier_2026-11-01`) | **Not MinGW** — the frozen stage2 (`C:/dev/p3new/stage2.exe`, built 2026-10-27) miscompiles Simple semantics (Option transport kept where `T?` narrowing was needed). Same class existed on the **MSVC** stage2 of 2026-09-01 (`windows_msvc_stage2_rejected_struct_receiver_route_threads_2026-09-01.md`) and on **Linux x86_64** (`linux_stage2_reexport_stats_ud2_2026-09-27.md` SIGILL bare return, `linux_stage2_full_cli_hir_field_inference_2026-09-27.md`, `stage2_selfhost_native_entry_closure_request_open_segv_2026-10-05.md` "Blocks Stage 3 on Linux and Windows") | Per-record source workarounds + fixes (#6675/#6924/#6933 form); frozen stage2 needs a rebuild to absorb them |
| native-build in-process link AV | **Not MinGW** as far as recorded — the only linked AV with a root cause is S3N-7 (`LINK_NOTES.md:85`): inlined `std.env.env_get` passed a boxed text to `rt_env_get(ptr,len)`, `ucrtbase` memcpy AV; an extern-contract bug in Simple inlining (bug tag `stage2_inline_env_get_boxed_extern_abi_2026-11-03` in `LINK_NOTES.md`). No bug_db row named for an "in-process link AV" was found | Interim `llvm-objcopy --redefine-sym`; source workaround `io_runtime.env_get_nullable`; no dedicated owner found |
| stage2 exit 127 (`libLLVM-23.dll` clash, 0xC0000139) | **MinGW lane packaging** — `stage2.exe` dynamically imports `libLLVM-23.dll` + `libunwind.dll`; the first `libLLVM-23.dll` on PATH wins (`stage2_exit127_llvm_mingw_path_dll_clash_2026-10-26.md`) | Mitigated by `c235cc781b8` (PR #5084, bundle matching libLLVM DLL closure next to the stage exe); record still `open`; workaround = pin PATH order |
| Push gates timing out under host load | **Not MinGW** — `check-push-must-pass.shs` 60 s budget vs load (`fable_milestones.md:129,263`) | Operational; `.claude/rules/vcs.md` landing loop / admin merge |
| `bug_db.sdn` `.csm` conflicts slowing PR landing | **Not MinGW** — shared sealed file contention (`fable_milestones.md:263`) | Operational; add rows in a calm window or via the bug-status workflow |

## 2. Toolchain history: what actually bootstrapped on Windows

- **Seed (`bin/simple.exe`) has always been MSVC-ABI.** Every tracked redeploy names clang-cl /
  `x86_64-pc-windows-msvc`: `3fc45dacdf4` (2026-10-10, "clang-cl 23.1.1"), `bb3b1df8a59`
  (2026-10-26, "with clang-cl"), `18f447a6084` (2026-11-05, `SIMPLE_WINDOWS_ABI=msvc`).
  Verified on the artifact: `llvm-objdump -p bin/simple.exe` imports `VCRUNTIME140.dll` +
  `api-ms-win-crt-*`, linker version 14 (lld-link), 1 MB stack reserve; `rustc -vV` host is
  `x86_64-pc-windows-msvc`; `src/compiler_rust/.cargo/config.toml:42` pins `lld-link` for that target.
- **MSVC stage2 was attempted and rejected before the lane switch:**
  `windows_msvc_stage2_rejected_struct_receiver_route_threads_2026-09-01.md` — a 105 MB
  `stage2/x86_64-pc-windows-msvc/simple.exe` built and linked, then failed the stage-3 route probe
  (exit 3). So "it used to work on MSVC" is not supported by the record: no Windows stage3 has ever
  been admitted on either lane.
- **llvm-mingw UCRT became the default on 2026-10-23/24:** `f1badcd2355` (install pinned
  llvm-mingw via `bootstrap-prereqs.shs`), `f0afa5b2f81` (CLAUDE.md "never use GCC; Windows default
  llvm-mingw UCRT"), `da3e621ddc7` (`bootstrap-from-scratch.sh:1451-1458` defaults
  `SIMPLE_WINDOWS_ABI=gnu` under Git Bash), `1158d2f5d49` (CI ladder lane). The CI commit states the
  reason: the MSVC lane needed a Visual Studio environment (`simple-term-io build.rs` died on
  clang-cl/VCINSTALLDIR, phase-1 links failed LNK1120).
- **Current phase-3 chain is mixed:** seed = MSVC CRT; `C:/dev/p3new/stage2.exe` (2026-10-27) and
  `s3_fable43/44.exe` are llvm-mingw UCRT (`clang version 23.1.2`, `__mingw_*`,
  `_pei386_runtime_relocator`; stage2 imports `libLLVM-23.dll` and `libunwind.dll`; stage3 statically
  carries libunwind, imports only `api-ms-win-crt-*` + `dbghelp`). `LINK_NOTES.md:4`: "llvm-mingw
  20260922 UCRT clang + lld, --gc-sections". All three binaries use the same 1 MB default stack
  reserve, so the lane change did not alter stack size.

## 3. Failure classes vs ABI/toolchain plausibility

| Class | Reproduces off-Windows? | Root cause location | Win64 ABI / CRT plausibility |
|---|---|---|---|
| stage2 Option word in non-optional fields, `.?` not narrowing | Yes — Linux x86_64 stage2 records above show the same HIR/MIR type-narrowing family | `src/compiler/20.hir/*`, `src/compiler/50.mir/_MirLoweringExpr/*` (.spl) | None: the Option transport is one tagged i64 (`value_bits=0x1e55713b8c1`), passed in a register on SysV and Win64 alike |
| E-RTI-006 duplicate callee rows | Not yet run on Linux with the driver route; mechanism is a dangling text handle in a class-field bracket read | `src/compiler/20.hir/return_type_interface_v1.spl:523` | None: nondeterminism follows the file-worker route, not the CRT |
| `native_trait_owner_for_type` AV (#6933) | Same class recorded 2026-10-08 (`native_trait_optional_payload_identity_2026-10-08.md`), before the lane switch | `expr_dispatch.spl` ~6110/6120 (`_sffi_tuple_get_req<HirType>` kept the Option transport) | None (see above) |
| wild RIP after `rejected invalid array handle` | Consequence of the previous class (handle word reused as pointer) | same | None |
| in-process link AV | Not isolated; recorded instance is an extern arg-contract bug | bug tag `stage2_inline_env_get_boxed_extern_abi_2026-11-03` (`LINK_NOTES.md:85`) | CRT only as the crash site (`ucrtbase` memcpy), not the cause |
| stage2 exit 127 | Windows-only by construction (DLL search order) | packaging of `libLLVM-23.dll` next to `stage2.exe` | **Yes — MinGW-lane specific** (the MSVC seed is built without the `llvm` feature and imports no LLVM DLL at all) |
| MIR shard memory admission | Lane-independent policy | `src/compiler/80.driver` shard pool | None |

Linux riscv64 / aarch64 lanes: `linux_aarch64_stage2_cold_hir_generation_argument_mismatch_2026-10-02.md`,
`phase2_stage2_native_build_len_on_i64_aarch64_linux_2026-09-13.md` show the same stage2 codegen
class on SysV/AAPCS targets. No bug record attributes any of today's classes to `_MSC_VER` vs
`__MINGW32__`, SEH, emutls, `__chkstk` or long double. The only Win64 ABI-specific record is
`cranelift_win64_large_frame_stack_probe_2026-10-05.md` (Cranelift backend, fixed), not the LLVM
lane used by phase 3. `windows_unqualified_native_build_msystem_gnu_flavor_mismatch_2026-10-18.md`
(fixed 2026-10-19) was a flavor mismatch (`_fltused`, `__chkstk` undefined) — a link-selection
bug, not a miscompile.

## 4. Parameter passing and mangling (user question)

- The pure-Simple backend emits LLVM IR and lets LLVM apply the target convention; the backend
  has no hand-written Win64/SysV aggregate classification (`git grep sret|byval` in
  `src/compiler/70.backend` hits only `riscv_asm.spl` and the Cranelift/native isel; the 45 `sysv`
  mentions are the native x86_64 isel and ELF hash-style, not the LLVM lane). Because caller and
  callee of every Simple function are emitted by the same compiler for the same triple, a Win64
  hidden-sret / rcx disagreement would need two different producers; stage3 objects come from one
  producer (`LINK_NOTES.md` S3N lineage checks). For C-runtime calls, MSVC x64 and MinGW x64 share the
  Microsoft x64 convention for plain C aggregates; the differences (80-bit `long double`, C++
  non-trivial types) do not occur on the `rt_*` surface.
- Mangling is target-independent in both compilers: seed `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`
  and pure-Simple `src/compiler/70.backend/linker/obj_taker.spl:526 mangle_name` contain no
  `windows|msvc|gnu` branch; names like `transient_promote$T742` are accepted by COFF and ELF alike.
  The seed vs pure-Simple manglers can still differ by *algorithm* (that is the S3N duplicate-symbol
  history), but not by toolchain.

## 5. Source selection (SOSIX / platform layer) and the C runtime

- **No per-ABI source variants exist.** `git ls-files src/lib src/os src/runtime` has no
  `windows_gnu/`, `windows_msvc/`, `mingw/` or `msvc/` directory. The platform/SOSIX `.spl` layers
  branch only on OS: 22 `@when(os="windows")`, 13 `@when(os="linux")`, 0 on `target_env`.
  `target_env` reaches the compiler only in `30.types/_TypeLayout/layout_core.spl:282-332`
  (`PlatformAbi.Gnu|Msvc` parse/print) and the LLVM triple writer
  (`70.backend/backend/llvm_backend_tools.spl:425`). So the MinGW-built seed, stage2 and stage3 all
  compile the single `windows` variant; there is nothing less complete to fall into.
- **C runtime:** 392 owned files; `_MSC_VER` appears in 23 files / 83 lines, `__MINGW32__|__MINGW64__`
  in **0** files, `_WIN32` in 107 files. The MSVC-only branches guard intrinsics/SIMD dispatch
  (`runtime_simd_dispatch.c`), `_set_thread_local_invalid_parameter_handler`
  (`platform/windows_raw_mapping.h:14,27`), and SDK header selection
  (`platform/platform_win.h:20` `_MSC_VER || SPL_TOOLCHAIN_CLANGCL`). `runtime_fd_stat_v1.h:43-57`
  explicitly handles the UCRT-without-MSVC case. Under llvm-mingw, `windows_raw_mapping.h`'s
  invalid-parameter handler is compiled out — a behavioural divergence (invalid fd → CRT default
  handler) but not one linked to any of today's classes.

## 6. Does ABI/toolchain leak into canonical MIR, cache keys or source selection?

- **Source selection:** no leak (section 5).
- **Canonical MIR:** `MirTargetContext(arch, os, abi, backend)` carries `abi` (`30.types/cfg_decl_check.spl:111,261`,
  `platform_match.spl:25-28`), so MIR is target-contexted but the ABI value is only consumed at
  LLVM-IR emission; no MIR lowering branches on msvc/gnu (`git grep msvc|mingw|gnu` in `50.mir` and
  `20.hir`: 0 code sites).
- **Leak 1 — env-driven ABI at the backend:** `70.backend/backend/llvm_target.spl:23-43
  llvm_hosted_windows_env()` derives the triple's env from `SIMPLE_NATIVE_BUILD_TARGET`, then
  `SIMPLE_LINKER_FLAVOR`, then `SIMPLE_WINDOWS_ABI`, else `msvc`; `runtime_compiler.spl:54
  windows_link_flavor_select` mirrors it. The ABI is therefore a process-environment decision, not
  part of the target spec object.
- **Leak 2 — cache identity:** `80.driver/driver_build/incremental.spl:747 native_build_cache_scope_key`
  keys on backend/cpu/features/opt/compiler identity; the Windows ABI enters only via the
  environment-identity list (`80.driver/cache/native_build_environment_identity.spl:74,142`
  names `SIMPLE_LINKER_FLAVOR`, `SIMPLE_WINDOWS_ABI`), i.e. by env-var name rather than by triple.
  This matches the user's design concern (identity should come from triple + ABI spec) but it is
  a design gap, not the cause of any failure class above: the phase-3 lane never mixed ABIs inside
  one cache (`cgprobe/combined3` is gnu-only).

## 7. Would the MSVC lane help? Cost

- It would not fix any compiler-logic class (sections 1, 3): those are `.spl` bugs reproduced on
  MSVC stage2 (2026-09-01) and on Linux. It would remove the `libLLVM-23.dll` clash only by
  replacing it with the MSVC-era problems: VS environment dependency (`1158d2f5d49`), `_fltused`/
  `__chkstk` flavor mismatches (`windows_unqualified_native_build_msystem_gnu_flavor_mismatch_2026-10-18.md`),
  and a 105 MB MSVC stage2 that was itself rejected.
- Cost: rebuild stage2 (7,000-14,000 s per `fable_milestones.md:40` scale, 40-70 GB cap) plus
  every `cgprobe/combined3` object (gnu objects cannot link with an MSVC CRT), re-verify the
  C runtime's 23 `_MSC_VER` files under clang-cl, and keep the CI ladder on gnu — two lanes to
  maintain. Not recommended now; recommended instead: land #6933/#6921 into `s3_fable45`, keep the
  DLL-closure bundling (`c235cc781b8`) as the exit-127 fix, and file the two leaks in section 6 as
  a design todo (triple+ABI-spec cache identity).

## Evidence sources

`git log -- bin/simple.exe`; `llvm-objdump -p` and `strings` on `bin/simple.exe`,
`C:/dev/p3new/stage2.exe`, `C:/dev/p3new/s3new/s3_fable43.exe`, `s3_fable44.exe`;
`C:/dev/p3new/s3new/fable_milestones.md`, `LINK_NOTES.md`, `cgprobe/fable_drvfix7.ps1`;
`scripts/bootstrap/bootstrap-from-scratch.sh:1451-1458`, `bootstrap-phase-toolchain.shs:51-161`;
`doc/08_tracking/bug/*` records cited inline; `gh pr view 6933`.
