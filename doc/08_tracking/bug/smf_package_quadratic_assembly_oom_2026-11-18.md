# native-build `smf_package` OOM: SMF object assembly re-copied the whole prefix per module

**Date:** 2026-11-18  **Status:** FIXED in source (takes effect in a compiler built from it)
**Area:** `src/compiler/80.driver` — OutputFormat.Both (`--mode dynload`) SMF half
**Related:** `item5_native_object_resource_growth_2026_10_14` (object spool),
`stage2_whole_program_mir_memory_growth_2026-11-01.md`

## Symptom

Phase 3 (a Stage 2 compiler native-building `src/app/cli/bootstrap_main.spl`,
1593 modules, cranelift, `--mode dynload`, 14 MIR shards) passed every shard,
printed `[mir-shard] link modules=1593 objects=1465 objectless=128`, and the
linker wrote the 49 MB output (`simple.simple-native-build-<pid>-….tmp` plus
link receipt). The link worker then sat in `phase=smf_package state=running`
until the OOM killer took it at 52.4 G anonymous RSS. The staged output is
renamed to its final path only after the driver returns Success, so a fully
compiled and linked Stage 3 was lost.

## When the memory accumulates (measured)

Unit memory, one sample per minute (`p3i11b.mem.log`):

| time | phase | unit MB |
|---|---|---|
| 16:25:58 | hir (last go-to-end pass) | 15,917 |
| 16:26:58 – 16:29:58 | link | 30,334 → 31,945 |
| 16:30:58 | smf_package | 36,718 |
| 16:38:59 | smf_package | 37,755 |
| 16:39:59 | smf_package | 52,009 (cgroup limit; reclaim-bound from here) |
| 16:48:59 | smf_package | 53,686 → OOM |

About 16 G was already resident when the link started (link inputs; not SMF
packaging and not addressed here). The 20+ G that killed the process was
allocated inside `smf_package`.

## Root cause

`smf_object_spool_assemble_v1`
(`src/compiler/80.driver/driver_build/smf_object_spool_v1.spl`) concatenated the
per-module objects with

```
for name in spool.paths.keys().sort():
    ...
    out = bytes_concat_copy_v1(out, part.unwrap())
```

`bytes_concat_copy_v1` builds a fresh array holding `left + right`, so module
`k` copies the whole prefix of modules `1..k-1` again. The superseded `out` is
never reclaimed by the native runtime. Total copied **and retained** bytes are
the sum of all prefixes, about `N/2` copies of the image: quadratic in module
count. The object spool (item5) had moved the per-module bytes to disk, but the
assembly read them back through this fold.

The same fold shape was in `smf_parts_assemble_manifests_v1` and, three times
per dependency, in `serialize_smf_dependencies` (`smf_writer.spl`); with 1593
dependency entries that one retains a further ~0.4 G.

Nothing downstream needs the copies: packaging needs one contiguous image.

## Reproduction (the failing measurement)

Stage 2 from `pinned-394e392ed555` (`…/bootstrap-s2probe-integ14/…/stage2-admitted/simple`),
same env/argv as the Phase 3 recipe, 2 MIR shards, each run in
`systemd-run -p MemoryMax=12G -p MemorySwapMax=0`, link-worker RSS sampled every
~0.1 s and tagged with the progress phase. `sum_prefix` is the sum of running
totals of the `.smfpart` sizes in sorted order.

| entry closure | modules / objects | part bytes | sum_prefix | link-worker RSS at link end | `smf_package` growth | package wall |
|---|---|---|---|---|---|---|
| `src/app/stats/main.spl` | 87 / 74 | 3.5 MB | 0.14 G | 1.3 G | below sampler resolution | 0.4 s |
| `src/app/todo_scan/main.spl` | 142 / 123 | 6.3 MB | 0.45 G | 2.27 G | **+0.65 G** (peak 2.97 G) | 1.3 s |
| `src/app/cli/lint_entry.spl` | 397 / 354 | 23.1 MB | 4.59 G | 4.19 G | **+6.4 G in 11 s, OOM-killed at the 12 G cap; linked `.tmp` lost** | n/a |

Growth tracks `~1.45 x sum_prefix`, not part bytes: 2.8x the modules cost
10x the memory. The first Phase 3 shard of the following run produced 114
parts totalling 47 MB, so the full closure is on the order of 0.6 G of object
bytes and a sum of prefixes of several hundred G — unreachable under any cap.

## Fix

Append in place: one `out`, one pass, `out.push(byte)` per byte, in the same
sorted order. Applied to `smf_object_spool_assemble_v1`,
`smf_parts_assemble_manifests_v1` and the per-entry append in
`serialize_smf_dependencies`. Output bytes are unchanged (specs below compare
against the previous fold, which is kept as the reference
`smf_parts_assemble_objects_v1`).

### Before / after, assembly microbench

A standalone program that spools N objects of 200,000 bytes and calls
`smf_object_spool_assemble_v1`, native-built by the same Stage 2 (cranelift),
run under `MemoryMax=8G`. `put` is the same program without the assembly call.

| N x 200 kB | put only | assemble before | assemble after | checksum |
|---|---|---|---|---|
| 50 (10 MB) | 0.5 s / 80 MB | 16.3 s / 2,082 MB | 1.4 s / 168 MB | identical |
| 100 (20 MB) | 1.0 s / 158 MB | 61.8 s / 8,069 MB | 2.8 s / 334 MB | identical |
| 200 (40 MB) | 2.0 s / 315 MB | OOM-killed at 8 G | 5.5 s / 666 MB | — |
| 400 (80 MB) | 4.0 s / 628 MB | not run | 11.1 s / 1,331 MB | — |

Before: 4x per doubling. After: 2x per doubling.

## What this does not prove yet

A compiler-source fix only acts in a compiler built from it. The closure
measurements above used the unfixed Stage 2; a control run of the 397-module
closure with the fixed source tree and the same unfixed Stage 2 still fails the
same way (link-worker RSS 4.30 G at link end, 10.84 G after 10.8 s of `smf_package`, OOM-killed, no output). The microbench exercises the fixed functions as compiled
by Stage 2, not the Stage 2 link worker itself. The full-size confirmation is
the next Phase 3 run on a Stage 2 built from this change.

Residual, linear, not addressed here:

- a `[u8]` built by `push` costs 8 bytes per element in pure-Simple-compiled
  binaries (1 in the Stage 2 measured above), so a Stage 3-built compiler
  still holds ~8x the object bytes during packaging;
- in the default `code_only` mode `extract_code_from_object` reads only the
  first ELF of the concatenated image, so most of that image is never used;
- the ~16 G resident at link start.

## Publishing the linked output before packaging

Not done, by design. The staged output is renamed in the CLI layer
(`src/app/io/_CliCompile/compile_targets.spl`) only after the driver returns
Success and the functionless-artifact gate passes, and OutputFormat.Both is
fail-closed on its SMF half (`emit_both_smf_half_v1` returns a CodegenError).
Publishing first would leave a published binary behind a build that reports
failure. Making the SMF half non-fatal, or running it in a child process, is an
owner decision.

## Tests

- `test/01_unit/compiler/driver/smf_object_spool_spec.spl` — uneven, empty and
  out-of-order parts assemble byte-identically to the reference fold; manifests
  likewise.
- `test/01_unit/compiler/cache/smf_deps_validation_spec.spl` — the production
  dependency serializer emits the reference bytes for 40 entries.

## Microbench source

Placed at `src/app/smfpkg_bench/main.spl` for the measurement and not committed;
built with the Phase 3 `native-build` argv and `--entry-closure` on that file.

```
use std.io_runtime.{env_get_opt, file_read_bytes_result}
use compiler.driver.driver_build.smf_object_spool_v1.{smf_object_spool_begin_v1,
    smf_object_spool_put_v1, smf_object_spool_assemble_v1, smf_object_spool_get_v1}

fn bench_part(size: i64, seed: i64) -> [u8]:
    var out: [u8] = []
    var i = 0
    while i < size:
        out.push(((i + seed) & 0xFF).to_u8())
        i = i + 1
    out

fn bench_sum(bytes: [u8]) -> i64:
    var sum = 0
    var i = 0
    while i < bytes.len():
        sum = (sum * 31 + (bytes[i] as i64)) & 0xFFFFFFFF
        i = i + 1
    sum

fn main() -> i64:
    val n = (env_get_opt("BENCH_N") ?? "100").to_int()
    val size = (env_get_opt("BENCH_S") ?? "100000").to_int()
    val mode = env_get_opt("BENCH_MODE") ?? "assemble"
    val dir = env_get_opt("BENCH_DIR") ?? "/tmp/smfpkg_bench"
    var spool = smf_object_spool_begin_v1(dir)
    var i = 0
    while i < n:
        spool = smf_object_spool_put_v1(spool, "m{i}", bench_part(size, i))
        i = i + 1
    print "put n={n} size={size} err={spool.error}"
    if mode == "assemble":
        val all = smf_object_spool_assemble_v1(spool)
        if all.is_err():
            print "assemble error"
            return 1
        val bytes = all.unwrap()
        print "assembled len={bytes.len()} sum={bench_sum(bytes)}"
    0
```
