# Local research: SimpleOS filesystem toolchain and servers

Date: 2026-07-11

## Findings

- The RV64 HTTP wrapper sends real forwarded TCP requests, but no current
  `build/os/simpleos_riscv64.elf` exists. The retained June transcript is stale,
  and a fresh build currently stops because the selected compiler lacks LLVM.
- No SimpleOS database server exists. The DB checker only greps marker files;
  the historical `examples/11_advanced/simple_db` submodule is an explicitly
  unfinished skeleton with `pass_todo`.
- A 124,602,568-byte static SimpleOS Clang ELF exists at
  `build/os/clang_static/bin/clang_static`. It is not staged, the old bake is
  fixed at 32 MiB, and mounted executable reads cap at 4 MiB.
- Historical ring-3 success proves a small Clang-built output ELF. The SSH demo
  uses a boot preload and does not prove `/usr/bin/clang` ran from mounted FS.
- All canonical Simple role paths are already centralized in
  `initramfs_pack.spl`, `image_builder.spl`, and `disk_image_bake.spl`; reuse one
  target-native payload rather than adding compiler/loader variants.
- No target-native Simple payload currently exists. Existing image/spec evidence
  accepts marker ELFs or a 23-byte `SMF_FAKE_TARGET_SIMPLE`, and live self-host
  scenarios skip.
- Hosted launch metadata selects `filesystem`; only explicit
  `simpleos-baremetal` selects `baremetal_got`. The x86 filesystem bridge still
  has an unkeyed preload shortcut that can substitute `/FSEXEC.ELF` bytes.

## Historical anchors

- `894360a6198`: small on-disk ELF reaches ring 3.
- `d2d67b5960b`: SSH Clang-hello demo, but via boot preload.
- `8117e9bca20`: image role paths for the Simple compiler.
- `doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md`: real compiler
  execution remains open despite older closed state files.

## Current blockers

1. Pure-Simple deployed compiler is currently replaced by the Rust seed, and
   the fresh RV64 build reports LLVM unavailable.
2. Mounted executable range reads and per-`PT_LOAD` streaming are missing.
3. Real Clang/Simple payloads are not in a sufficiently large install image.
4. No guest DB service handles a real create/write/read request.

<!-- codex-research -->
## 2026-07-24 current-state reconciliation

The 2026-07-11 findings above are preserved as historical context. Later work
revived real web/DB traffic and filesystem Simple interpretation, but this
checkout contains none of the required current kernels, images, payloads, or
QEMU transcripts. Current completion therefore differs from the strongest
historical boundary:

| Requirement | Strongest historical evidence | Current status |
|---|---|---|
| RV64 web + DB | One real QEMU boot answered `/health` and `/`, then completed `CREATE`/`INSERT`/`SELECT` with `codex-41`. | HISTORICAL PASS; CURRENT UNVERIFIED |
| Filesystem Clang | OVMF-launched filesystem Clang emitted a valid x86-64 `ET_REL` object that was retrieved and host-linked/run. | HISTORICAL PARTIAL; CURRENT FAIL |
| Filesystem Simple | A later ring-3 filesystem interpreter run read `/HELLO.SPL`, printed `Hello from SimpleOS`, and exited zero. | HISTORICAL PARTIAL; CURRENT FAIL |
| Filesystem loader provenance | Source/unit contracts reject unkeyed preload and marker substitution. | SOURCE PASS; CURRENT LIVE UNVERIFIED |

The later interpreter PASS supersedes the earlier `rt_string_join` failure as
history, but it does not prove a current payload. Guest-native Simple
compile/link/run and complete compiler/loader role execution have never passed.
Filesystem Clang has never linked and executed its output inside the guest.

The canonical current RV64 service proof remains:

```text
SERIAL_LOG=<artifacts>/serial.log DB_QUERY_LOG=<artifacts>/db_query.log sh scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --with-storage --with-db
sh scripts/qemu/check_simpleos_rv64_db_server.shs --artifacts <artifacts>
```

The wrapper sends real TCP requests and checks three HTTP 200 responses plus
`OK CREATE`, `OK INSERT`, and `codex-41`. Generic filesystem-exec QEMU marker
specs do not prove web or DB behavior.

The strongest Clang history is commit `7cf0b6aec3a`; revival anchors include
`aa9f7d1278`, `a5fdae0384`, and the current filesystem/server restorations
`c2ef3b878b`, `e3a7c19530`, and `9c3d3a4680`. The target remains
`x86_64-unknown-simpleos` with the SimpleOS sysroot, static runtime, and
filesystem `PT_LOAD` streaming. The next live Clang proof must extend object
emission to guest LLD linking and execution of the linked filesystem ELF.

### Stage 4 prerequisite discovered on 2026-07-24

No current target/image proof may start until an accepted pure-Simple Stage 4
CLI exists. A fresh compiler-only candidate passed the 40-file synthetic memory
gate at 136,196 KiB, but one guarded real full-CLI closure reached the 16 GiB
cap after only 103 of 1,314 files. The retained owner is the complete set of
rich parsed `Module` values held until batch HIR lowering, not the per-file
flat parser scratch arenas.

The reviewed minimum repair is a two-pass low-memory entry-closure pipeline:

1. Parse each file and retain only an independently owned compact
   `ModuleSurface` needed for imports, re-exports, callable/type/enum/impl
   signatures, constants, and trait defaults.
2. With every surface installed, parse one full Module at a time, lower it to
   HIR, and remove the rich Module from retained compiler state.
3. Retain HIR for the existing MIR layout prepass and later compilation.

Per-module flat-arena snapshots, another deep AST copy, and source-order
lowering were rejected: the flat bridge already deep-converts each Module, and
HIR resolution requires a complete cross-module declaration surface.

Before another Stage 4 attempt, require:

- a surface-extraction unit proving ordinary bodies are absent;
- a native forward re-export/enum/trait-default fixture;
- 10 ordered post-release real-closure markers averaging at most 25,000
  retained heap objects/file.

After Stage 4 admission, reproduce RV64 web/DB first, filesystem Simple second,
and filesystem Clang guest link/execute last. This order revives known working
boundaries before extending the two incomplete toolchain lanes.

#### 2026-07-24 allocation follow-up

The first streaming implementation released each rich `Module`, but the live
no-GC registry still grew by 38,913 objects/file. A brace-free string fast path
reduced that to 37,602, still above 25,000. Phase probes attribute nearly all
growth to ordinary body parsing; surface extraction adds only 73--128 entries.
The next bounded slice therefore keeps the existing parser and conversions but
omits only top-level function bodies during Phase 2. Trait, class, and impl
methods and all non-function declarations remain on the rich parser path.
The admitted slice passed the live gate at 10,332 objects/file.
