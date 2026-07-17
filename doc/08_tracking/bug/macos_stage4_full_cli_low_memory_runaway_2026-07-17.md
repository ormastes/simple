# macOS Stage 4 full-CLI compile exceeds bounded resource envelope

## Status

Open. Apple Silicon Stage 2/3 self-host succeeds. The whole-tree Stage 4
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
