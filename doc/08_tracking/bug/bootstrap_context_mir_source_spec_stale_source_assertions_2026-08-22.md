# `bootstrap_context_mir_source_spec` is a stale source-text spec, not a link failure (2026-08-22)

**Status:** FIX IMPLEMENTED — reviewer GO pending.

The run8 deploy gate flagged `test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl`
(16 examples, 12 failures) and the failure text starts with
`error: LLVM native linking failed: Linking failed: cc linking failed:`, which
reads like a toolchain problem. It is not:

- The spec never links anything. It `rt_file_read_text`s
  `driver_bootstrap.spl`, `driver_aot_native_output.spl`, `driver_types.spl`,
  `driver_aot_pipeline.spl`, ... and asserts that those SOURCES contain fixed
  snippets; the "cc linking failed" string is inside the *expected* text block
  (`driver_native_link_undefined_symbols` rendering) that the spec was written
  against.
- Controls: deployed seed `dee19c5` 16/12; candidate `1c8757fb745` 16/12;
  candidate with `. scripts/setup/llvm-toolchain-env.shs` sourced
  (`CC=clang-23 LD=ld.lld-23`, LLD 23 first on PATH) **still 16/12** — the
  toolchain is irrelevant.
- Failing examples: "uses requested native-build entry module for bootstrap
  MIR lowering", "lets Stage4 reach the full pure Simple native output path",
  "uses source fingerprints instead of raw module cache hits for native
  dynload", "keeps bootstrap HIR lowering keyed and named by the requested
  module", ... — i.e. the driver sources were refactored today (object-cache
  entry fix 809ce6d4e71, HIR registry memo, CodegenTarget fix) and the frozen
  snippets no longer match.

Action: re-baseline the snippets against the current driver sources, or
replace the text assertions with behavioural ones (the object-cache
second-build spec already covers the cache half). Not a deploy blocker;
`scratchpad/fp8/gate.sh` treats it as tree-side.

## Resolution (2026-08-22)

The spec now pins the current owned contracts instead of deleted implementation
shapes:

- deterministic entry selection through `bootstrap_entry_source_index`;
- frozen native-capsule construction and authenticated cache updates;
- cache-hit HIR registry replay with the entry bit carried explicitly;
- Stage-4 context dispatch while the diagnostic direct-IR route remains
  explicitly gated;
- current three-argument MIR accumulator and SSA-transformed stored function;
- current LLVM entry-symbol, trailer, call-callee, and aggregate pointer
  normalization owners.

The frozen Rust seed was
`/mnt/data/worktrees/simple-main/src/compiler_rust/target/release/simple`, SHA-256
`022dc1df80c3afdafcd78119f71eb23dabb0c9598951f03669c4c129baa78f7c`, against
source revision `5b850a11c5ec17f292d51050ba20b8dd7d47e19b`.

The test reads through the typed `std.nogc_sync_mut.fs.read_text` facade rather
than declaring `rt_file_read_text`. Its shared structural-contract helper
requires producer-before-consumer ordering. A dedicated mutation test removes
the producer, removes the consumer, and reverses their order; all three
sabotages are rejected, so the helper is not a tautological source-presence
check.

The bounded review cycles converged from 4/16 to 12/16, then 16/17, and finally:

```
SPEC FILE VERDICT: test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl outcome=OK declared>=17 executed=17 passed=17 failed=0 skipped=0 dropped=0
Results: 17 total, 17 passed, 0 failed
PASS test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl
```

No full-suite or already-green criterion was rerun.

## Oracle hardening after second review

The 17/17 result above predates the final oracle-quality review and therefore
does not close the current postimage by itself. The spec now extracts the exact
owning function body, removes full-line and inline comments plus docstrings,
requires exact producer/consumer occurrence counts, and requires producer before
consumer. Entry selection, frozen-capsule compilation, Stage-4 dispatch, cache
receipt publication, MIR accumulation, and indirect-call normalization are
checked inside their respective functions rather than across an entire file.

The mutation example operates on the loaded production
`bootstrap_lower_to_mir_context` source. Removing its reset, removing its entry
registration, or swapping their order must each flip the same real oracle from
true to false. Status remains review-pending until an independent focused run
and reviewer GO validate this hardened postimage.
