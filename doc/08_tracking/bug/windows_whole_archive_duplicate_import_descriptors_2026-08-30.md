# Windows whole-archives the runtime unconditionally, multiplying import descriptors

- **Date:** 2026-08-30
- **Status:** ANALYSED, not yet applied — the patch is specified below and is
  deliberately held until the lane reaches the link
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
