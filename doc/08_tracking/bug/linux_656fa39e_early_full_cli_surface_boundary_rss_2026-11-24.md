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
