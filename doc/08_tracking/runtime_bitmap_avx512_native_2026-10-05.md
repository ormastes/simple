# Production bitmap AND: native AVX-512 evidence

Scope: the existing production C runtime kernel and its public dispatch wrapper.
This does **not** qualify Simple DB/application invocation, Phase2-emitted app
code, dynamic loading, bitmap OR, performance, or unavailable-hardware fallback.
No kernel implementation is changed by the accompanying test package.

## Run the bounded check

```sh
sh scripts/check/check-runtime-bitmap-avx512-native.shs
```

Requires Linux x86-64, Clang (or a compatible `CC` executable), Perl and GDB.
The script creates a private temporary directory and retains source/binary
hashes, compiler identity, compile/run logs and a watchdog receipt. Compilation
and both runs share a 180-second/5859375-KiB process-tree limit. It does not use
Cargo or modify a bootstrap runtime authority.

Exit 77 means **UNSUPPORTED**, never PASS. The forced-kernel harness checks the
production AVX512F CPU predicate and OS extended-register-state predicate before
calling any AVX-512 function. The public-dispatch test runs only after that
check passes. Missing tools, build errors, mismatches, signals, or missing GDB
kernel-entry evidence fail the check.

## Actual evidence collected before relocation

Host: WSL Ubuntu on Intel Xeon W-2135, with AVX512F/DQ/CD/BW/VL. Production CPU
and OS-state predicates both returned true. Source `runtime_simd_dispatch.c`
matched release `d8455b2c00b589be71971679d7649231d4ce86c1` exactly:

- Git blob: `86f474a3b5039f9d2ee853735ec992aacf0be6b4`.
- SHA256: `d42249d298bbc054b05dab2b90d80b8c0afdf5058e175a35839c199b2f49bb71`.

The forced-kernel test includes the unchanged production translation unit and
calls its actual `db_bitmap_and_avx512` through a volatile function pointer.
It passed 816 cases and 35760 word comparisons: 17 lengths from zero through
129, eight alignment offsets, six rotations of zero/one/high-bit/max/alternating
U32 patterns. Its independent oracle uses division/remainder arithmetic.
All inputs were preserved; 94800 output positions outside active spans retained
canaries. The printed `canary_slots=130560` counts all scanned positions, including
active positions separately checked against expected values. Canaries do not
prove absence of out-of-bounds reads. The called function's disassembly contains
ZMM `vmovdqu64` and `vpternlogq` instructions.

The public test creates six real runtime arrays using `rt_array_new`/`rt_array_push`
and calls `rt_db_bitmap_and_u32` for lengths 8, 9 and 17. All 34 tagged result
words matched the independent oracle; outputs were fresh and inputs unchanged.
An external GDB breakpoint recorded **three entries** into the production
AVX-512 kernel. The inferior and GDB both exited successfully. This proves the
public dispatch selection on this host, not a forced replacement of dispatch.

Original private artifacts, retained by the collecting session:

| Check | Directory | Executable SHA256 |
|---|---|---|
| Forced kernel | `/var/tmp/item5-avx512-bitmap-native-guard` | `7a95569215c1353053639ff276a199395cb314d6f2ba10a62d22d0ff47a91119` |
| Public dispatch | `/var/tmp/item5-avx512-bitmap-public-guard` | `5424abb5ff22a0966292bbf04cf54c30b6fc4de4ef6de583c220b315a44c74af` |

Each directory contains `compile.log` and `run.log`. No performance claim follows
from the short wall-time measurement.

## Packaging verification and limits

The relocated sources are byte-identical to the actual tested harnesses:

| File in `src/runtime/test` | SHA256 |
|---|---|
| `rt_db_bitmap_avx512_selfcheck.c` | `ac300327af2353fcff492c7f74310e84d3dbaa08ccd6f990cf9cafdc28d90a5e` |
| `rt_db_bitmap_dispatch_selfcheck.c` | `e21807be68e409ae7ab87e8f040a100089534f2194478dd061f7740d27b2557c` |
| `rt_db_bitmap_dispatch_selfcheck.gdb` | `5c2d09fa85586fdb77b10070cc3dd7d48ac92f8c7fbf3fef3919152496648fd3` |

Shell syntax checking passed. A distinct negative build of the unchanged forced
harness with `SIMPLE_RUNTIME_FORCE_NO_X86_XSTATE=1` reported `UNSUPPORTED` and
returned 77. This checks the safety gate, not execution on a physical non-AVX
machine. Its artifacts are in `/var/tmp/item5-avx512-package-negative-guard`.
The complete newly packaged wrapper has not been run: doing so would repeat
the already-green native criteria. Their results above are carried forward by
identical source hashes, not represented as a fresh packaged-wrapper run.
