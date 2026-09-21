# macOS Stage 4 full-CLI compile exceeds bounded resource envelope
## Source fixed; native verification pending — audited 2026-09-21

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Source corrections are present; bounded Stage 4 acceptance remains open.
The historical run below reported Apple Silicon Stage 2/3 self-host success. The whole-tree Stage 4
runaway is now traced to two sync regressions, but the corrected compiler
rebuild currently stops at the separately tracked missing `copy_mem` provider.

## Reproduction

From a clean `main` workspace on `aarch64-apple-darwin`:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --deploy --jobs=half
```

The exact Stage 4 command is recorded in:

- `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`
- `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build-low-memory.log`

## Current evidence

- Rust seed, native-all, and compiler-backfill archives rebuild successfully.
- Stage 2 passes compiler sanity, SHA-256
  `81795487d5889aba3cf9c5b1059553f5f934176fedabc2dee9baeacb5281f53e`.
- Stage 3 passes compiler sanity, SHA-256
  `10a28c2d789c19f7450ff4bfbde5b9ad9aee1639bb9e3b6b35bcf20c3d6110e2`.
- The initial two-worker Stage 4 attempt was killed by macOS with signal 9
  after about 21 minutes, before a linker child or output binary appeared.
- A one-worker `--low-memory` attempt bounded most observed RSS between 5 and
  9 GiB, with a brief observed peak near 14.3 GiB. It was stopped at the
  mandatory 63-minute ceiling after about 52 CPU-minutes. It still had no
  linker child, output binary, or diagnostic output.
- The retained native cache contained 1,424 module objects during Stage 4.
- A phase-profiled retry from `main` exposed a second sync regression in
  `bootstrap_main.spl`: it pre-enabled closure mode and passed four source
  roots. The driver loaded 10,502 aliased sources in 1.257 seconds, then was
  terminated while parsing an unrelated lint module. Peak RSS was 296 MB.
- The corrected entry-only wrapper and hosted `rt_remove` provider produced a
  new 24 MiB Stage 3 compiler. The next compiler rebuild reached the linker and
  failed only on `_copy_mem`; the three-cycle cap stopped further retries.

## Root cause found

The intended Stage 4 path seeds only `src/app/cli/main.spl`, clears the
pre-enabled closure flag, and expects `CompilerDriver.load_sources_impl()` to
walk imports before enabling closure mode. One sync regression restored a
`not has_project_source` guard on that walk. A second restored the old wrapper
that set closure mode to `1` and supplied `src/compiler`, `src/app`, `src/lib`,
and `examples/10_tooling` as inputs. Together they bypassed pruning and expanded
the graph to either the whole tree or 10,502 path aliases.

The correction removes the location guard and restores entry-only wrapper
inputs while retaining explicit-entry, AOT-mode, and not-already-closure
guards. Source-contract regressions pin both halves. The bounded Apple Stage 4
acceptance run remains required after the `copy_mem` provider gap is fixed in a
fresh verification turn.

This is not a missing provider-symbol failure: Stage 4 did not reach the exact
provider-capsule linker. The previous missing hosted signal symbols were fixed
separately by `runtime_hosted_signal.c`, and the focused runtime tests pass.

## Expected

The clean Apple Silicon Stage 4 compile reaches the exact capsule linker,
produces the full CLI, passes source-check/redeploy admission, and remains
within a documented time and peak-RSS budget on a 24 GiB host.

## Acceptance criteria

1. Add phase timing and peak-RSS evidence around full-CLI closure, lowering,
   object emission, capsule projection, and final link.
2. Remove the dominant repeated work or retained state; do not raise the
   runaway ceiling as the primary fix.
3. On a 24 GiB Apple Silicon host, one clean exact Stage 4 run reaches the
   linker and produces a candidate within the agreed bounded time/RSS target.
4. The candidate passes `-c`, source-check, redeploy, MCP, and LSP smoke gates.
5. Preserve strict `SIMPLE_NO_STUB_FALLBACK=1` and exact provider ownership.

## Current main and PR #1207 audit, 2026-09-21

Fetched main `e0dd873da1b` and PR #1207
`fix/astra-stage3-hir-20260921` at `6a7a22ddc37`. Both already contain the
documented correction. The relevant owners are byte-identical across them:

| Owner | SHA-256 | Current contract |
|---|---|---|
| `src/compiler/80.driver/driver_source_pipeline_loading.spl` | `1a9a4339ca98f02ac2f6f60c4ced9eda23e2c2dba4b2defd2cfba5933d4f3ee3` | Lines 192–201 select explicit/native entry closure without the historical location guard; lines 477–479 seed only the requested entry; line 636 walks its imports. |
| `src/app/cli/bootstrap_main.spl` | `5c1b60249a5cec9255047da94b2df3ee1b0d1f49d0868084951004825f631` | `run_native_build_bootstrap` clears the closure flag and supplies `entry_path` through one array input and one scalar input. |

No duplicate source fix is needed. The database's prior `closed` status was
unsupported by this report and is corrected to
`fix-implemented-verification-pending`.

The bounded contract
`test/01_unit/compiler/bootstrap/native_entry_closure_mode_contract_spec.spl`
now reads the current owners, scopes wrapper assertions to the native build
route, and rejects the historical location guard, pre-enabled closure flag,
and whole-tree seed list independently. It also rejects a missing route.
Previously it searched `driver.spl` for obsolete local variable names.

An inline Python source-text replay extracted the seven literal predicates
from the updated Simple helper and checked current source plus all four
negative controls. Result: PASS, 0.04 s wall time, 16,990,208 bytes maximum
RSS on macOS (`/usr/bin/time -l`). The three historical mutations each changed
their target text and failed the contract. This is a bounded structural audit,
not SSpec execution, compilation, a native behavior reproducer, or proof of
the full Stage 4 resource envelope. The remaining broad July source-contract
case in `stage4_smoke_gate_spec.spl` also contains obsolete ownership/name
assertions and is not counted as passing evidence here.

### Performance, memory, and SoSIX assessment

This follow-up changes tests and tracking only. There is no production
algorithm, allocation, process, file, environment, or host-interface change,
so no new reciprocal runtime profile is warranted or claimed. The required
paired Stage 4 elapsed/peak-RSS measurements remain pending and the historical
GiB/minute values above are not treated as current results. No full bootstrap
or compiler execution was attempted.

The existing fix routes the same platform-neutral entry/closure data through
the existing compiler and environment owners. This follow-up introduces no
OS predicate, macOS API, POSIX/libc import, runtime primitive, or alternate app
implementation. It therefore adds no SoSIX compatibility delta under the
one-app/one-host-interface rule. This is a source-boundary audit, not a SoSIX
execution claim. The old `copy_mem` blocker is historical evidence; its current
resolution is not established by this lane.
