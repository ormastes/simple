# Windows whole-archives the runtime unconditionally, multiplying import descriptors

- **Date:** 2026-08-30
- **Status:** APPLIED 2026-09-06 — all three patch items are now in the tree, and
  the duplicate-descriptor failure is reproduced and shown gone by real links on
  a real Windows 11 box. See "Application + evidence (2026-09-06)" below for what
  is proven and what is not.
- **Supersedes the "Blocker B" open question in**
  `bootstrap_stage2_windows_link_unresolved_rt_and_dup_kernel32_2026-08-24.md`

## The failure

    simple_native_all.lib(kernel32.dll) : error LNK2005:
      __IMPORT_DESCRIPTOR_kernel32 already defined in simple_native_all.lib(kernel32.dll)

MinGW shows the same defect as 22 `multiple definition` errors from `ld`.

## Measured cause

`simple_native_all.lib` (354 MB, 4,606 members) contains **582 members named
`kernel32.dll`**, and `__IMPORT_DESCRIPTOR_kernel32` is defined **4 times**
(also `bcryptprimitives` x3, `api-ms-win-core-synch-l1-2-0` x2). These are
rustc-synthesized `raw-dylib` import libraries — one per crate declaring
raw-dylib imports — all bundled into a single staticlib. They are NOT the
vendored windows-rs import libs: those hold ~1,350 kernel32 members each, and
the strings `windows.0.` and `/DEFAULTLIB:windows.0.*` appear zero times in the
staticlib.

Ordinary lazy archive resolution pulls exactly one. `linker.rs` whole-archives
the runtime archive **unconditionally on all three Windows lanes**, which forces
all four in.

**Linux does not have this bug because Linux does not do this.** It uses
selective retention roots and only whole-archives behind an env escape:

| element | location |
|---|---|
| `runtime_retention_symbols` (5 hardcoded roots, each kept only if defined in the archive) | `linker.rs:557-604` |
| `add_elf_undefined_roots`, emits `-Wl,-u,<sym>` | `linker.rs:607-612`, `cfg(linux/freebsd)` |
| macOS equivalent `-Wl,-u,_<root>` | `linker.rs:1414-1415` |
| the gate: `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` else roots + plain archive | `linker.rs:1459-1476` |

Roots are needed on Linux because it also passes `-Wl,--gc-sections`
(`linker.rs:1502-1504`).

## Why Windows whole-archives at all

**No evidence it was ever justified.** `git log -L` and `git log -S` over those
lines return only tree-wipe and restore commits — the history is destroyed. The
surrounding comments justify only the `/link` *spelling*, never the *semantics*.
The one recorded Windows symptom (~72 unresolved `rt_*`) came from the archive
being DROPPED entirely, not from lazy extraction. Windows looks like retained
legacy that never received the retention migration.

## Patch plan

1. `linker.rs` ~1443-1456 — replace each whole-archive spelling with
   archive-as-ordinary-input plus retention roots, keeping the old path behind
   `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` for parity with Linux:

   | lane | archive input | root flag |
   |---|---|---|
   | clang-cl | lib path into `clang_cl_link_args` | `/INCLUDE:<sym>` in the SAME `/link` group |
   | clang GNU-driver / MSVC | `cmd.arg(lib)` | `-Wl,/INCLUDE:<sym>` |
   | MinGW | `cmd.arg(lib)` | `-Wl,-u,<sym>` |

   Symbol decoration was MEASURED, not assumed: `nm` on the real archive prints
   `T rt_api_surface_extract` and `I __IMPORT_DESCRIPTOR_kernel32` bare. x64
   `extern "C"` is undecorated. (32-bit x86 would need a leading `_`; this lane
   is x64-only.) `add_elf_undefined_roots` is cfg-gated out on Windows, so a
   sibling emitter is required.

2. `linker.rs:1383` (`libspl_objects.a`) — LEAVE whole-archived. Those are
   program objects with no import members.

3. The bare `/WHOLEARCHIVE` in the stub-fallback path has **no `:lib`
   argument**, so it whole-archives every input archive and recreates the
   collision class. Narrow or remove it in the same change.

## Risks, stated plainly

- Members reachable only through constructors/registration with no static
  relocation can be dropped. Linux has soaked exactly these semantics with the
  same five roots, and `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` remains the escape.
- **`read_defined_symbol_set` fails OPEN** (`linker.rs:498-500` returns an empty
  set when `nm` fails), which would silently yield ZERO retention roots and drop
  the entire archive. On this host `llvm-nm` fails with rc=127 unless
  `/c/dev/tool/msys2/mingw64/bin` is first on PATH (the DLL-shadowing trap), so
  this hazard is live. Any implementation MUST verify with
  `SIMPLE_TRACE_RUNTIME_ROOTS=1` and assert a non-empty root set rather than
  trusting the default.
- **Interaction with the unresolved-`rt_*` blocker: orthogonal, cannot worsen
  it.** A referenced-but-undefined symbol errors identically under either mode;
  dropping whole-archive only shrinks the set pulled in. This fixes the
  duplicate-descriptor blocker only.

## Application + evidence (2026-09-06)

Host: real Windows 11 Pro box, `C:\Users\ormas\dev\simple`, HEAD `a12a19eb775`.
Linker: MSVC `link.exe` driven by `clang-cl` 18.1.8
(`C:/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin`). Note the msys2
`mingw64/bin/clang-cl.exe` on this host is **broken** (`error while loading
shared libraries: ?`, rc=127) — the DLL-shadowing trap this doc warned about is
real; the LLVM-18 msvc install was used instead.

Archive under test is the real one:
`build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple_native_all.lib`
(354,514,522 bytes).

### State found

**Patch items 1 and 2 were already committed** at `a12a19eb775` — the Status
line above was stale. `linker.rs:1509-1566` already carries the retention-root
rewrite for the `selected_runtime` / `is_native_all` site, the
`SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` escape, and the fail-closed
"no runtime retention roots resolved" error that answers the `read_defined_symbol_set`
fail-open hazard. Item 2 (`archive_path`, the program-objects archive) is
correctly still whole-archived.

**Only item 3 was outstanding**, carried in-source as a `NOTE (not changed here)`.

### Change applied

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` (~line 1854):
removed `clang_cl_link_args.push("/WHOLEARCHIVE".to_string());` from the
clang-cl stub-fallback path, keeping `/FORCE:MULTIPLE,UNRESOLVED`. The stale
`NOTE (not changed here)` comment was replaced with a removal rationale. One
line of behaviour; no other file touched.

### Real link transcripts

BEFORE — bare `/WHOLEARCHIVE`, exactly the item-3 spelling:

    clang-cl m.obj simple_native_all.lib -o before.exe /link /WHOLEARCHIVE
    rc=96, 5803 lines, 18 x LNK2005
    simple_native_all.lib(kernel32.dll) : error LNK2005: __IMPORT_DESCRIPTOR_kernel32 ... already defined in simple_native_all.lib(kernel32.dll)
    simple_native_all.lib(kernel32.dll) : error LNK2005: __NULL_IMPORT_DESCRIPTOR_kernel32 ... already defined in simple_native_all.lib(kernel32.dll)

AFTER — same inputs, bare `/WHOLEARCHIVE` removed (lazy archive resolution):

    clang-cl m.obj simple_native_all.lib -o after.exe /link
    rc=0, 0 lines of diagnostics, 0 x LNK2005
    after.exe: 108,032 bytes, runs, exit 0

Item-1 semantics were re-proven on the same host for completeness:

    /link /WHOLEARCHIVE:<lib>                      -> rc=96, 18 x LNK2005 (the old spelling)
    <lib> as ordinary input + 5 /INCLUDE: roots     -> 0 x LNK2005

That second link additionally proves all five roots are genuinely DEFINED in
this archive: `/INCLUDE:<name>` on an undefined name is itself a hard
unresolved-external error, and none of the five appears in that link's
LNK2001/LNK2019 list. That discharges part of the "assert a non-empty root set"
risk above without running the driver.

(The five roots are the hardcoded `runtime_retention_symbols` set:
`__simple_runtime_init`, `__simple_runtime_shutdown`, `rt_set_args`,
`rt_function_not_found`, `rt_string_bytes`.)

### What is NOT proven — stated plainly

- **No end-to-end `native-build` run.** The Rust seed cannot be rebuilt on this
  box: `cargo check --release --bin simple` fails with two **pre-existing,
  unrelated** errors — `E0433: unresolved module or unlinked crate 'libc'` at
  `compiler/src/interpreter_extern/file_io.rs:2522` and `:2546` (`libc` is not a
  Windows dependency of that crate). That is a separate defect in a file this
  lane must not touch. So the edit is validated at the linker-semantics level
  and by name resolution over `linker.rs` (which produced no diagnostics), not
  by executing the modified driver.
- **The item-1 "new spelling" hand link does not link to completion.** It clears
  every LNK2005 but still ends rc=96 on 107 x LNK2001 / 93 x LNK2019 unresolved
  externals — pulling `__simple_runtime_init` drags LLVM archive members whose
  C++/system dependencies a bare two-argument hand link does not supply. That is
  an artifact of the toy link, not evidence about the real driver, which adds
  the stub object and system libs.
- **Not a full Stage-2 link**, and no claim is made about the separate
  unresolved-`rt_*` blocker; as this doc already argued, the two are orthogonal.
- `/FORCE:MULTIPLE` on the stub-fallback path would have demoted LNK2005 to a
  warning anyway, so item 3 was never the source of the *recorded* error — it
  was a latent recreation of the same collision class. The transcripts above
  deliberately omit `/FORCE` so the collision is visible.
