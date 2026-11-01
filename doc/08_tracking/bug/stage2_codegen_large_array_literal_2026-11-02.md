# Stage2 LLVM codegen blows up on large module-level array literals

- **ID:** stage2_codegen_large_array_literal_2026-11-02
- **Priority:** P1 (blocks phase-3 whole-program build)
- **Status:** open (workaround landed in the source module; compiler fix pending)
- **Binary:** frozen stage2 `C:/dev/p3new/stage2.exe` built from `ef0681fc0e1`
- **Runs:** phase-3 runs 20b and 21 (dynload `--emit-archive`, 32 MIR shards)

## Symptom

Both runs were killed at the 97 GB cap at the same point: LLVM codegen of
`lib.common.search.generated.unicode_17_0_0`
(`src/lib/common/search/generated/unicode_17_0_0.spl`, 120 KB, generated).
The trace (`C:/dev/p3new/r11/build.log.err`) shows thousands of
`MIRB-AGG enter ... arm=array operands=316/928...` lines. Earlier modules
codegen in 2-27 s.

The module holds 17 module-level `[i64]` array literals, up to 3127 elements each
(about 25,000 elements in total). Stage2's array-aggregate MIR/LLVM lowering
grows superlinearly in memory with operand count.

## Workaround (this change)

`unicode_17_0_0.spl` now stores each table as a comma-separated `text` constant
(`_unicode_<name>_text`) and decodes it once through a memoized accessor
`_unicode_<name>() -> [i64]` (module `var` cache plus a ready flag). All tables were
private, so only internal call sites changed (`_unicode_x[i]` became `_unicode_x()[i]`).
The public API is unchanged. The module carries
`# @workaround bug=stage2_codegen_large_array_literal_2026-11-02`.

A spec hook `unicode_table_samples_for_spec()` returns `[len, first, mid, last]`
for each table. `test/01_unit/lib/common/search/unicode_17_0_0_text_tables_spec.spl`
compares those against the values taken from the original literals. The existing
`unicode_17_0_0_spec.spl` checks the every-scalar fingerprint and the full
NormalizationTest corpus.

## Follow-ups

1. **Generator:** `examples/05_stdlib/spipe/tools/unicode/generate_unicode_tables.mjs`
   must be updated to emit the text-table and accessor form. Until then,
   regenerating will bring the literals back. Also update
   `unicode_table_generator_sha256`.
2. **Compiler fix:** make array-aggregate lowering linear (emit a constant global
   initializer for all-constant `[i64]` literals instead of per-operand aggregate
   construction). After that, revert the workaround.
3. **Other large module-level literals in the stage3 closure** (by comma count;
   not changed here, re-check them if codegen stalls on these modules):
   - `src/lib/common/web/public_suffix_data.spl:11` `[text]` ~10.4k
   - `src/lib/gc_async_mut/gpu/browser_engine/html_named_character_references.spl:11,2245` `[text]` ~2.2k each
   - `src/app/cli/query_error_pattern_matcher.spl:24,100,176,252,328` `[u16]` ~1.16k each
   - `src/lib/common/image/webp_vp8_decode.spl:1244,1342,1440` `[i64]` ~0.9-1.05k
   - `src/compiler/15.blocks/blocks/unicode_classification_v17.spl` is 2 KB with no
     large literal, so it is not affected.

## Verification

Stage2 probe, 16 GB cap: `native-build --entry-closure --entry
src/lib/common/search/analyzer.spl --emit-object`. The results are in the PR description.

Result (2026-11-02, `measure.ps1 -CapGB 16`, 8 threads):
`first_obj_s=266.3 total_s=322.2 peak_tree_GB=3.86 objs=12 killed=False`.
The `unicode_17_0_0` object (`aot-a0ee9ab1...o`, 170 KB, its receipt names the
module) was written about 1-2 s after the previous object (the probe ran without
`SIMPLE_COMPILER_TRACE`, so it has no `MIRB-AGG` lines to compare). The final `-o` COFF relocatable merge fails with rc=1 because
ld.bfd is not installed. That failure is environmental, not codegen, and the
reference `C:/dev/p3new/cgprobe/common_api` probe hits it too.

Data parity: after stripping the declaration syntax, the 17 table bodies are
byte-identical to the original literal bodies (`cmp`). Apart from the `()`
accessor calls, the function bodies are unchanged. No table contains a negative
value. The decoder accepts only digits and commas.

The SPipe specs could not be run on this host. `bin/simple.exe` is the Rust seed
and fails to parse an unrelated file (`windows_redirected_process.spl`). Stage2
has no `test` command. A native driver executable built with the
`core-c-bootstrap` bundle failed to link (`rt_process_spawn_session` is
undefined), also environmental.
