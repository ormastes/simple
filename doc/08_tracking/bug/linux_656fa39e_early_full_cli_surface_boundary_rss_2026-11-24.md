# Linux early full CLI exceeds RSS cap after surface release, 2026-11-24

Status: unresolved performance incident. The process-tree RSS failure is
established; the responsible allocation substep is not. No source optimization
or successful full-CLI qualification is claimed by this report.

## Immutable lineage and evidence

- Source: `656fa39e28a7775da0172a4e8eeeea1ac0ea59f0`.
- Pure-Simple Phase2 producer SHA256:
  `21ab99e0cb58fe6dd806db1d43ff8be45c1112f0da372ee4c2f6e95c92d798bf`.
- Original producer run: [45326410090](https://github.com/ormastes/simple/actions/runs/45326410090),
  binary artifact `14893961542`. The retained parent qualification compiled and
  executed native LLVM Hello before this dependent build. Its executable hash
  is `f74460f5c1b64a87c56e4b046ebf1405d3502a3ba14f0030efe6ab466b4403e8`.
- Failed dependent run: [45340259012](https://github.com/ormastes/simple/actions/runs/45340259012),
  [early full-CLI job 138263574007](https://github.com/ormastes/simple/actions/runs/45340259012/job/138263574007).
  Control revision: `9c1de732ab6c0a57c1bed650ee65e55175584844`.
- Artifact: `linux-656fa39e-full-cli-45340259012`, ID `14896906651`,
  1,662,701 bytes, ZIP SHA256
  `f6e6c93f2df19f326fe39774c6626ae62204dd238445bfaedd2e03195b4a7677`.
- Same-source runtime archives: `libsimple_native_all.a` SHA256
  `37bede8d0ea74ac722e00e7100b9c63e3004abb11c6c346a0d37264d2255ab88`;
  `libsimple_compiler_backfill.a` SHA256
  `6a46ebc25c9051d81d9a82b9a6815eb1b93a2e7d66600cb3d1c888663be164b4`.
- Tool snapshots record Ubuntu clang/LLD/llvm-ar 18.1.3, invoked through the
  actual driver paths. `tool-files.json` seals their resolved executable bytes.
- Durable local evidence:
  `D:/dev/simple-user-storage/build/release-bootstrap-20261123/evidence/linux-656-fullcli-45340259012/`:
  `artifact.zip`, `artifacts.json`, `job.log`, `build.stdout`, `build.stderr`,
  and `diagnosis.json`. The ZIP was downloaded once and verified against its
  published digest and size. A Windows long-path extraction failed; the
  complete ZIP was inspected directly, without treating partial extraction as
  the artifact inventory.

GitHub artifacts expire. The ZIP and its checksum are the retained evidence;
the run URL alone is not a permanent archive of these bytes.

## Actual product and owner

The compiler ran `native-build` with LLVM, target
`x86_64-unknown-linux-gnu`, `--runtime-bundle core-c-bootstrap`, the explicit
matched runtime path, `--threads 1`, `--profile=prod --release --strip`,
`--managed-build-phase=phase4 --opt-level=standard --low-memory`,
`--entry-closure`, entry `src/app/cli/_CliMain/main_and_help.spl`, and
`--mode dynload`. `build.argv.json` retains every argument and absolute path.

The full source set was `src/compositions/cuda_static`,
`src/compositions/kernel_llvm_cranelift`, `src/compiler`, `src/app`, `src/lib`,
`src/os`, `src/plugins`, `src/package_ownership`, and `src/compositions`.
Caches/storage were isolated to this child. The configured low-memory worker
route was actually selected: stdout reports the per-file worker pool with
per-module linking, one worker, and a unit of four picks. This was not a
whole-program build or a narrowed product.

| Observation | Value |
|---|---:|
| Host available memory at admission | 15,145,256 KiB |
| Enforced tree cap (75% available) | 11,358,942 KiB (10.83 GiB) |
| Minimum outside-cap reserve policy | 2,097,152 KiB |
| Observed peak tree RSS | 11,475,256 KiB (10.94 GiB) |
| Finite owner timeout | 14,400 seconds |
| Actual terminal | `rss-cap-exceeded`, exit `88` |
| Quiescent / RSS enforcement | `1` / `1` |
| Selected physical sources / logical rows | 4,184 / 7,124 |
| Retained native objects / module terminal records | 0 / 0 |

Admission was recorded at 06:39:38 UTC; the controller failed at 06:44:24 UTC.
This was an RSS kill, not expiration of the four-hour limit. The owner's
coordinator reservation estimate was 2,049,260 KiB, and worker estimate was
3,145,728 KiB; these are admission estimates, not measured per-process peaks.
The tree peak does not establish which process or allocation owned the growth.

The four actual selected paths were `src/lib/common/encoding/unicode_scalar.spl`,
`src/lib/common/types.spl`, `src/lib/nogc_sync_mut/sffi/system_env_core.spl`, and
`src/lib/common/io/types.spl`. The worker reports
`[unit-tldr] unit=0/1@0~h0 parsed=4 summaries=0 fallbacks=0 import_hir_lowered=0`.
No semantic error diagnostic or product executable was observed. Product
version/run/test/native-Hello qualification therefore did not run.

## Last observable boundary and limits of attribution

The worker loaded 7,124 logical rows, then emitted surface-release messages
through `seq=4184`. The final released path was
`src/lib/nogc_sync_mut/driver/error.spl`. There is no observed HIR/MIR completion,
native-object publication, or completed module receipt after this boundary.

The retained source snapshot is
`scv-revision-v2-17c04bba14f9225bacc050bfb5e1fa76cb628a1f358ce67052c142e53e98ee20`.
Its snapshot marker, inventory, and receipt are retained under
`scv-source-metadata/`; all three hashes in `index.json` were checked. Inventory
SHA256 is `cf3a87c652629771bdf63419aacc3ce80c0b2f46df40616a7e260e9c0958b8bf`.
The unit index header independently records `n=7124`. The terminal controller
record says `immutable_inputs_after=PASS`.

In the frozen source, `driver_source_parse_streaming.spl` reconstructs retained
`SourceFile` records after the release loop, then calls
`ModuleSurfaceBuilder.finish_into`, which calls `module_surfaces_freeze`, and
then promotes the retained registry. This log has no internal boundary samples
that distinguish those operations. It does **not** prove that freeze alone
caused the RSS excursion, nor that any one array-copy or ownership hypothesis
is its cause.

The freeze-index/memo optimization `b6cb8348216096f751a8effcf03ae1592c9b24b6`
is already an ancestor of the frozen source. Reapplying that change is not a
new remedy for this incident.

## Falsifiable follow-up, not an executed check

A separately authorized bounded attribution check would preserve this exact
producer/runtime, source snapshot, complete 7,124-row graph, and four picks.
Sample the worker and simultaneous tree RSS at retained-source reconstruction
entry/exit, `finish_into` entry, `module_surfaces_freeze` entry/exit, and registry
promotion entry/exit. Stop at the existing cap and retain which boundaries
actually completed. A freeze-specific hypothesis is supported only if the
measured increase occurs between its own entry and exit; growth before entry
or after exit refutes that attribution. An interrupted interval remains
unresolved. No such check or fourth product dispatch is authorized by this
report, and no cap increase is proposed.

## Related but distinct observations

- [November whole-program full-CLI peak RSS](full_cli_native_build_peak_rss_2026-11-13.md)
  describes whole-program AST/HIR retention and two MIR workers. Those causes
  are not established for this one-worker per-file incident.
- [October retained-parser incident](phase3_full_cli_low_memory_retained_parser_2026-10-12.md)
  is a different producer/route observation.
- [October surface-freeze timeout](surface_freeze_full_cli_timeout_2026-10-11.md)
  concerns deadline expiry, not this enforced RSS failure.

The preceding two control attempts failed before compiler launch (first a
generic-LLD version probe, then an omitted hidden cache file during artifact
transfer). Those harness failures remain separate from this actual compiler
resource failure. The retained parent native Hello was reused, not repeated.
The independent Phase3 job was left running; this incident does not give its
verdict or formal admission status.

## Attribution (2026-11-25, Windows rb5)

The same boundary was reproduced four times on Windows at source
`0285176e3a7b` ("rb5 pin"), streaming-surfaces route, `--entry-closure`, entry
`src/app/cli/main.spl`, 3,840 closure modules / 7,124 logical rows, with two
different compilers (one seed-built, one Simple-built). The worker holds about
10 GB through every `phase2:surface:file:*` line; immediately after
`phase2:surface:file:released ... src/lib/nogc_sync_mut/driver/error.spl seq=3840`
its private bytes grow about 12 GB/min to 63 GB and it is killed.

### Observed stack (measured)

Three all-thread dumps taken 8 s apart during the growth (cdb, resolved through
the linker map) all show, innermost first:

```
rt_array_push
compiler.hir.hir_lowering.module_surface_registry_index.module_surface_registry_index  (+0x194 .. +0x234)
module_surface_import_resolution_trace_with_generation_v1  (+0xe65)
module_surfaces_freeze  (+0x17c5)
ModuleSurfaceBuilder.finish_into
CompilerDriver.parse_all_streaming_surfaces_in_place_impl  (driver_source_parse_streaming.spl)
parse_all_committing_impl
stage_parse
```

An earlier IP-only sample of the same moment was in
`rt_core_is_registered_immortal_ptr`. This places the growth inside
`module_surfaces_freeze`, in `module_surface_registry_index`, which answers the
"freeze entry/exit" question of the follow-up above for the Windows run.

### Mechanism (by reading; not re-run)

Both this pin and the Linux source `656fa39e` predate `94d86930de6`
(PR #11343, merged 2026-11-24T14:29Z). In that older text
`module_surface_registry_index` opens with

```
val names = registry.ordered_names
val indices = registry.ordered_indices
```

A `val`/`var` whose initializer is a place read of an existing array is given
a private copy by native lowering: `maybe_copy_array_value` in
`src/compiler/50.mir/mir_lowering_stmts.spl` emits `rt_array_len`,
`rt_array_new(len)` and an inline `rt_array_get` + `rt_array_push` loop; the
seed emits `rt_array_copy` for the same shape
(`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`). So every lookup
copied both complete alias arrays, about 2 x 7,124 x 8 bytes = 114 KB, inside
`finish_into`'s transient scope where nothing is released until the scope
ends. Freeze performs several tens of lookups per import (up to 30 candidate
probes for a `std.` import). The inline copy loop is what produces a
`rt_array_push` frame called directly from `module_surface_registry_index`,
and `rt_array_new` is `rt_core_array_new_fill`.

Status of each claim:

- Proven by reading: the two copy bindings exist at `0285176e3a7b` and at
  `656fa39e`; native lowering copies such bindings with a push loop; the copies
  are per lookup and unreleased within the scope.
- Measured elsewhere, not here: PR #11343 reports, on a Darwin native
  producer, 24,000 lookups over 120 names growing the footprint 52,887,600
  bytes before the change and 16,384 after, with the hash table built once.
  That is 2.2 KB per lookup at 120 names, which scales to the 114 KB above.
- Proven by disassembly (`llvm-objdump -d` on the rb5 Stage 3 binary
  `fbd55c5ef93a`, symbol `module_surface_registry_index` at `0x140dbf5e0` per
  `simple-p3-stack64.map`): the sampled return addresses `+0x194`
  (`0x140dbf774`) and `+0x234` (`0x140dbf814`) are literally the two
  `callq rt_array_push` (`0x141b21c10`) sites inside the two entry copy loops
  for `val names = registry.ordered_names` (`0x28(%rax)`, loop
  `+0x160..+0x1a4`) and `val indices = registry.ordered_indices`
  (`0x30(%rax)`, loop `+0x200..+0x244`). Both loops execute before
  `if names.len() != indices.len()` at `+0x246` (`0x140dbf826`), settling
  that the sampled growth is the per-lookup entry copies rather than the hash
  table fill loops.
- Not supported: a repeated index rebuild. No term of `cache_hit` changes
  inside one freeze: the transient scope identity is constant (freeze opens or
  ends no scope, pause preserves the identity, and
  `rt_session_alloc_begin/end` only move a depth counter), the session id is
  constant, `registry.generation` is assigned once before the import loop, and
  freeze never appends to `ordered_names`/`ordered_indices`. A rebuild is also
  cheap: `rt_array_push` grows by doubling `realloc` in place
  (`rt_core_array_reserve`), so one build of 16,384 buckets + 7,124 chain
  slots is about 190 KB, not quadratic. The observed rate does not
  discriminate between the two mechanisms (both need 1-2 thousand calls per
  second), so the rate is not cited as proof. Repeated rebuild was not
  measured on Windows at 7,124 names.

### Remedy and what is not verified

`94d86930de6` already removes both copies on `release/1.0.0`; no further
source change is made here. For the rb5 pin the same source change is a
backport of that commit's `module_surface_registry_index.spl` hunk. The copy
is native-only and invisible to the interpreter, so it is pinned by the
source-contract test in
`test/01_unit/compiler/hir/module_surface_registry_linear_guard_spec.spl`;
`test/01_unit/compiler/20.hir/module_surface_freeze_perf_parity_spec.spl` now
also pins one index build per freeze. Neither the pin with the backport nor
the release tip was re-run through the full-CLI boundary, so "RSS stays flat
after the last surface release" remains unverified on both hosts.
