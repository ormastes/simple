# Hosted + libsimple_native_all: Rust argv family overrides the C array owner, args silently empty

Status: fix-implemented (C runtime). P1.
Parent class: `dynamic_runtime_lane_dual_rt_definitions_2026-09-06.md`
Component: `src/compiler_rust/runtime/src/value/args.rs:248`, `src/runtime/runtime_native.c:7896-7931`

## Reproduction

The run-13 Stage 2 compiler (sha256 `ef163123…ae5a`) builds
`build/repro/r3/main.spl`, a program that only prints
`sys_get_args().len()`:

```
--backend=cranelift --runtime-bundle host-gpu \
  --runtime-path <run-13 phase2-runtime-capsules/ef16…>
```

`./r3gpu x y` prints `direct=0` and no diagnostic.

The link line is the host C objects followed by
`<capsule>/libsimple_native_all.a`, with `--allow-multiple-definition`.

## Mechanism

- `simple_entry.o`'s `main` calls `spl_init_args(argc=3)`.
- `runtime_native.c` declares `rt_get_args`, `sys_get_args`, `rt_cli_get_args`
  and `rt_set_args` as `SPL_WEAK`. The Rust archive defines strong
  `#[no_mangle]` versions, and a strong archive definition beats a weak object
  definition. So `sys_get_args` goes to Rust `rt_get_args`.
- Rust `rt_get_args` calls `rt_array_new`, which resolves to the C version
  (C is strong and appears first). It then calls Rust `rt_array_push_grow`,
  which C does not define.
- `rt_array_push_grow` type-checks the C-allocated array against Rust's
  `HeapObjectType::Array`, fails, and returns 0 (seen in gdb). The array
  stays empty.

## Why not fixed with the sibling row (original assessment, superseded below)

Making C's argv family strong on ELF would collide with the seed's
exact_stage4 lane. That lane links the C runtime beside the Rust capsule
without muldefs (see the `rt_set_args` comment, `runtime_native.c`). The
designed fix is the 09-06 one: project the Rust archive so that every name the
C objects define is ceded. COFF already does this
(`llvm_runtime_owner_c_archive_v1` / `_c_gnu_archive_v1`). There is no ELF
equivalent.

## Unblock condition

An ELF owner=c projection of `libsimple_native_all.a` in the hosted
cranelift/GNU link path. Pin it with the same
`rt_cli_args_owner_order_selfcheck.c` linked against the projected archive.

## Does it affect the deploy? (2026-11-07)

**The deployed compiler: no.** The Stage 3 link
(`scripts/bootstrap/resume-stage3-from-admitted.sh:1016`,
`bootstrap-from-scratch.sh:5777`) and the Stage 4 full-CLI link
(`bootstrap_native_build_main`, `bootstrap-from-scratch.sh:2888`) all pass
`--runtime-bundle core-c-bootstrap`. For that bundle,
`native_all_allowed_for_runtime_bundle`
(`70.backend/backend/llvm_native_link_hosted_support.spl:234`) is false. An
`execve` trace of the same probe, built with core-c-bootstrap (both dynload
and default mode) against the run-13 `stage2-runtime-authority`, shows that the
link line has C objects only and the probe prints `direct=3`.

**The bootstrap gate: yes.** `bootstrap-phase-verification.shs:2562` builds
`compiler_cli` (`src/app/cli/_CliMain/main_and_help.spl`) and `test_runner`
with `tool_runtime_bundle=host-gpu` against the hosted runtime authority. That
is a required PASS row of `stage2-compiler-tests` (run 13 log: "slim stage-2
profile is missing a required PASS row for compiler_cli_build"). Run 13 failed
that row in the build itself, after 10156 s. Run 14 is building it now. When
the build succeeds, those tools start with argv empty.

## Root cause (refined)

`native_all_gnu_support_args`
(`70.backend/linker/_LinkerWrapper/native_all_support.spl:112`) adds
`-u rt_vulkan_provider_is_available`. That root lives in the simple_runtime
CGU `...cgu.12.rcgu.o` of the authority archive, which also defines
`rt_set_args`, `rt_get_args`, `sys_get_args` and `rt_get_argc` strongly
(`value/args.rs:248` and following). A second CGU, `cgu.07`, carries
`rt_cli_get_args`, `rt_cli_arg_count` and `rt_cli_arg_at`
(`value/cli_sffi.rs:58`). The C copies at `runtime_native.c` were `SPL_WEAK`
on ELF, so `nm` placed all seven in the Rust range.

## Fix

The C array owner, the one #7376 settled, now also wins beside the Rust
archive. In `runtime_native.c`, the whole argv family (`rt_set_args`,
`rt_get_args`, `sys_get_args`, `rt_get_argc` and the `rt_cli_*` trio) is
strong under this condition (`SPL_ARGV_FAMILY_OWNER`,
`SPL_ARGV_RUST_ARCHIVE_PEER`):

```
defined(__ELF__) && defined(SIMPLE_RUNTIME_MEMORY_OWNER) && !defined(SIMPLE_CORE_C_STANDALONE)
  && !defined(__simpleos__) && __STDC_HOSTED__
```

The SimpleOS sysroots (`src/os/port/llvm/sysroot.shs:214`,
`scripts/os/simpleos-sysroot-{aarch64,riscv64}.shs`) also omit STANDALONE.
There, `simple_core/core_process.spl` owns argv
(`os/libc/simpleos_cli_args.c`), so the guard excludes them. The independent
review found this; without the exclusion they would have had two strong owners,
and `spl_init_args` <-> `rt_set_args` could have recursed.

Among hosted ELF composers, only the native_all composition is compiled under that condition.
`runtime_compiler.spl` adds STANDALONE exactly when no archive is linked
(`include_dynload = native_all == ""`). The native_all link always carries
`--allow-multiple-definition` (`llvm_hosted_allow_duplicate_definitions`;
Stage 4 rejects native_all) and lists the C objects first, so the first (C)
definition wins.

The original objection was the exact_stage4 lane. That lane does not meet the
condition, because `tools.rs:818` always passes STANDALONE, so it keeps the
weak copies. Truth table from `nm runtime_native.o`:

| defines | binding |
|---|---|
| `MEMORY_OWNER + STANDALONE` | `W` |
| `MEMORY_OWNER` | `T` |
| none | `W` |
| `MEMORY_OWNER + __simpleos__` or `-ffreestanding` | `W` |

### Why not ELF projection

The projection is unworkable in the lane that matters. Phase-verification tool
builds are strict managed links (`SIMPLE_MANAGED_NATIVE_TOOL_AUTHORITY_*`), and
`native_runtime_strict_archives_v1` admits only the sealed authority archive.
A link-time projection therefore fails closed there, and a projection made
when the authority is produced means rewriting the sealed-authority pipeline.
Rust `#[linkage = "weak"]` would be the first nightly feature in the runtime
crate.

## Evidence (2026-11-07)

- **Link-level check, real archive:** the third lane of
  `src/runtime/test/rt_cli_args_owner_order_selfcheck.c` uses the run-13
  authority `libsimple_native_all.a`, linked with
  `-u rt_vulkan_provider_is_available`, `--gc-sections` and
  `--allow-multiple-definition`. It uses no `-lsqlite3` and no
  `--whole-archive`. The entry calls `spl_init_args`, like the hosted shim.
  - Before the fix: `FAIL rt_get_argc=0 want 3`, plus `rt_array_len=0 want 3`
    for `sys_get_args`, `rt_get_args` and `rt_cli_get_args` (`FAIL — 4 of 6`).
  - After the fix: `PASS — 6 argv provider checks, argc=3`, with all seven
    symbols in the C range.
  - The two C-only order lanes still pass. With no archive, the lane reports
    `ERROR — nothing was checked`.
- **End to end:** the same run-13 compiler and archive, with
  `--runtime-bundle host-gpu`, compiling this tree's `src/runtime`, went from
  `direct=0` to `direct=3`.

## Known gaps

- **Mach-O:** there is no `--allow-multiple-definition`, so the C copies stay
  weak there and a macOS host-gpu link is not fixed by this change.
- **`--runtime-owner=rust` (ELF A/B lane):** C argv now wins there too; the
  ELF composer emits no rust-owner define to key on.
- **The selfcheck archive lane is not wired into a gate:** it needs the
  authority archive path. With `-DSELFCHECK_EXPECT_NATIVE_ALL=1` it exits 2
  when the Rust member is absent, so it cannot pass vacuously.
- **COFF:** already ceded (`coff_runtime_owner`, #7376).
- **Not addressed here:** the run-13 Stage 2 compiled the C runtime with
  `/usr/bin/cc` (gcc on this host) and linked through collect2. That breaks
  the never-GCC rule.
