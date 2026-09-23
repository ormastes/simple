# Stage 4 retained parser memory audit, 2026-09-22

Status: **OPEN / runtime verification blocked**. No production code changed;
this is a status correction and executable follow-up probe, not a memory fix.
The frozen source baseline is `e0dd873da1b7828389db4eb60e82972cc8245313`.

## Overlap and source findings

- PR #1282 (`9ef8fd5caf8`) owns retained HIR promotion/scratch retirement. Its
  body explicitly states native ownership, RSS, and backend checks unavailable.
  This lane does not duplicate those changes or interpret its source tests as
  a Stage 4 parse-memory pass.
- PR #1285 owns process parse-shard environment selection. Its body explicitly
  states that Windows runtime scenarios did not execute.
- `a323583b0dc` added transient parser string reclamation;
  `07d2ac8834d` and `e7380eaee50` later wired an experimental scoped entry path.
  These historical commits are not an admission of the current path.
- Current `driver_source_pipeline_parsing.spl` routes retained entry modules
  through `parse_full_frontend_selected_v1`. The scalar provider in
  `parse_result_provider_seam_v1.spl` passes `false` to
  `parse_and_build_module_scoped`. That helper starts a transient scope only
  when its boolean argument is true. Streaming surface extraction instead
  starts/ends an outer scope and promotes registry/surface owners. A helper
  name or historical commit cannot establish the active ownership lifecycle.

## Attempted Windows reproduction

Host: Windows x86_64. Producer:
`D:/simple_build/bootstrap-msvc/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`.
SHA-256: `4a8dd3eb3887b9cb61608dd6cc668dafa18bbd75bd0d98326328df48c6d54db5`.
Version: `simple-bootstrap 1.0.0-rc.1`. Its adjacent `admission.env` matches
that hash; `git-state-before.env` reports `b94c58f06dc12dab8fa9e33387da731312e4bcdf`
with dirty fingerprint `1d5ebf13ce5a2a319d1f87a0c6df89a10dbc1948161c4d4b8b35f2698ff6babb`.
This is an older admitted Stage 2 producer, not a Stage 3 compiler rebuilt
from the frozen source or from PR #1282.

Four fresh-process attempts used 2/16 synthetic modules, 6,263/49,218 source
bytes, 128 arithmetic statements per module, and a checksum-bearing entry.
`SIMPLE_BOOTSTRAP_STAGE4=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and one worker were
set. Command shape:

```text
<producer> native-build --backend <cranelift|llvm> --source <fixture-dir> --entry-closure --low-memory --threads 1 --entry <fixture-dir>/main.spl -o <fixture-dir>/probe.exe
```

The existing Windows Job Object collector enforced 20 seconds, a one-second
termination grace, and a 1 MiB combined-log cap. psutil sampled the sum of
collector descendants' working sets at 20 ms intervals. This is a sampled
process-tree peak, not the OS exact peak; wall time includes collector startup.

| Backend | Modules | Wall seconds | Sampled tree peak bytes | Exit |
|---|---:|---:|---:|---:|
| Cranelift | 2 | 2.000 | 26,849,280 | 1 |
| Cranelift | 16 | 0.406 | 22,421,504 | 1 |
| LLVM | 2 | 0.578 | 29,716,480 | 1 |
| LLVM | 16 | 0.516 | 23,420,928 | 1 |

All four emitted exactly:
`Error: Stage4 entry must be src/app/cli/main.spl or src/app/os/main.spl`.
No executable existed, and no semantic control ran. These figures measure
refusal, so neither scale ratios nor time/RSS improvements are admissible.
The compiler log SHA-256 is
`2a02d80d4107ba2878c55c275e07c3596860999879cea04fc949a2a1c85d9108`.
Local logs and measurements remain under
`D:/simple-p1-parse-mem-0922/build/native_probe/stage4-parse-memory/`.

## Concrete follow-up test / TODO

New executable probe:
`test/02_integration/compiler/stage4_parse_memory_scale_probe.spl`.
It invokes the retained entry-closure parse path on 2 and 16 modules with
128 functions each. After all parses, it checks every function name, body,
and exact integer return value. Expected checksum: 32,640 / 2,096,128.
The negative case must reject malformed source with a recorded parser error.
Cache is disabled and actual parse work must be at least the module count.
This validates retained AST semantics; it does not validate emitted machine
code, HIR lifetime, the whole CLI closure, or RSS by itself.

Required artifact: an admitted native producer with matching source/runtime
receipts, plus a probe executable built from each compared source revision.
Building a changed compiler source as input to the same old compiler and
measuring that old compiler does not exercise its changed driver logic.
The probe links the driver under test into the measured executable.

Run in each isolated baseline/candidate checkout, using its own output/cache.
Unset inherited `SIMPLE_BOOTSTRAP_STAGE4` for this noncanonical probe entry;
this program calls the parser directly and is not the full Stage 4 transaction.

```sh
env -u SIMPLE_BOOTSTRAP_STAGE4 SIMPLE_NO_STUB_FALLBACK=1 \
  "$PHASE_COMPILER" native-build --backend "$BACKEND" \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 1 \
  --entry test/02_integration/compiler/stage4_parse_memory_scale_probe.spl \
  -o "$PROBE"
"$PROBE" --baseline
"$PROBE" --scaled
"$PROBE" --invalid
```

Run each probe invocation under the host process-tree collector, fresh process,
120-second timeout and 1 GiB tree RSS ceiling. Both positive invocations must
exit 0 and print `semantic_ok=true`, the expected module count/checksum, and
nonzero parse work. The negative invocation must exit 0 and print
`stage4_parse_memory_invalid_rejected=true`. Missing output is failure.
Before accepting a fix, compare the same fixtures on original/candidate
executables: candidate wall time and sampled peak RSS must each be at most
110% of baseline at both sizes. Across the 8x module count, scaled time and
RSS must each be at most 10x the small case, and absolute ceilings still apply.
These proposed admission bounds are not measured results.

After the probe passes, the original canonical Stage 4 full-CLI transaction
still needs its own phase-correlated process-tree RSS trace and executable
CLI/test-runner semantic smoke. Do not close this bug on the small probe alone.

| Required path | Current evidence |
|---|---|
| Windows x86_64 Cranelift | Entry refused; native probe build/run pending |
| Windows x86_64 LLVM | Entry refused; native probe build/run pending |
| Common retained parser driver | Source reviewed; native semantics/time/RSS pending |
| Linux x86_64 original Cranelift Stage 4 | No accessible phase artifact in this lane; pending |
| macOS/FreeBSD, AArch64/RISC-V, remaining backends | Not executed; no regression verdict |

The bug remains open. No claim of regression freedom spans unexecuted hosts,
CPUs, backends, or the separate streaming/HIR paths.
