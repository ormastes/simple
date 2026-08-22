# HIR per-module cliffs were the CODEC, not lowering — `HirCodecWriter` was O(n²) — 2026-08-22

## Status
RESOLVED 2026-08-22 — `HirCodecWriter` accumulates into bounded chunks.
Measured on the real `src/compiler/50.mir/hwir/zca_rows.spl`, one process, one
tree, one binary: `hir_module_encode` **1,139,353 ms -> 6,702 ms (170x)**, blob
byte-count identical at 1,331,200.

## Symptom
Stage1 bootstrap run12 (tree `c6f190752ff`, seed `5ff4999c8e9`) showed extreme
per-module cliffs in the HIR phase (step 2/6), against a ~1-3 s median:

| module | `[build] hir` completion `dt=` |
|---|---|
| `compiler.mir.hwir.zca_rows` | 1,543,271 ms |
| `compiler.frontend.core.lexer_struct` | 925,384 ms |
| `compiler.10.frontend.core.types` | 607,244 ms |
| `compiler.mir.mir_aop_injection` | 457,134 ms |
| `compiler.mir.hwir.frontend` | 441,714 ms |
| `compiler.frontend.core.aop` | 397,937 ms |

Six prior sessions (recorded in `hir_phase_per_module_cost_2026-08-21.md`)
attacked import registration, registry scans, and symbol-table copies. Those
were all real, but none of them was this.

## The measurement that redirected the whole investigation
The run12 log carries BOTH a `[hir-prof]` line (emitted by the lowerer, at
`hir_phase_profile_module_end`) and the `[build] hir` completion receipt
(emitted by the driver after the module is fully processed). Differencing them
per module says how much time was spent OUTSIDE lowering:

| module | completion `dt=` | profiled lowering `total=` | gap |
|---|---|---|---|
| `compiler.mir.hwir.zca_rows` | 1,543,271 ms | **7,826 ms** | 1,535,445 ms |
| `compiler.backend.backend_types` | 2,670,990 ms | 248,188 ms | 2,422,802 ms |
| `compiler.backend.backend.interpreter` | 1,940,251 ms | 177,345 ms | 1,762,906 ms |
| `compiler.frontend.core.lexer_struct` | 925,384 ms | 74,184 ms | 851,200 ms |

Lowering `zca_rows` costs 7.8 s. The other 1,535 s is after it. The only
substantial work the driver does there is `hir_cache_store` ->
`hir_module_encode` (`driver_hir_cache.spl:171`).

Confirmed directly by a standalone probe (parse + lower + encode of that one
file, no closure, deployed seed, `SIMPLE_EXECUTION_MODE=interpret`):

    PROBE parse=98548ms lower=8610ms encode=1139353ms blob=1331200 funcs=30

**Encode was 132x lowering.** The SIGPROF sampler (`SIMPLE_INTERP_SAMPLE=1`,
219,026 samples) named it unambiguously — self time, not inclusive:

    124636  56.90%  put_i64        <- SELF
     18213   8.32%  put_bool       <- SELF
     26535  12.12%  hc_enc_hir_expr

56.9% of the entire run inside `HirCodecWriter.put_i64`'s own body, which is one
`self.parts.push(...)`.

## Mechanism: a COW deep-clone per push, caused by one parameter hop
`put_i64` is a one-line push. It cost ~430 us/call here versus ~7 us/call in a
micro-probe, so the cost is not the push — it is a deep clone of `parts`.

Isolated in a 20-line probe (`SIMPLE_PERF_COUNTERS=1`), same binary, 80,000
pushes into the same class, differing ONLY in how the writer reaches the frame
that mutates it:

| shape | pushes | `SELF_FIELD_ARR_COW_CLONES` | elements cloned | wall |
|---|---|---|---|---|
| `fill(w, n)` then `w.put(...)` directly | 80,000 | **4** | 120,000 | 0.57 s |
| `top(w)` -> `mid(w)` -> `leaf(w)` -> `w.put(...)` | 80,000 | **80,000** | **3,199,960,000** | 595 s |

One clone per push, of the whole array. Per-block wall time rose 13.6 / 86.6 /
202.9 / 292.6 s across four equal blocks — textbook O(n²).

The trigger is **one extra parameter hop**, not call depth as such: calling
`w.put(...)` directly on a parameter binding is clone-free (the write-back
replaces the caller's value and drops the old `Arc`), but passing that parameter
on to another function leaves an intermediate frame holding a live `Arc` on
`parts` for the whole traversal, so `Arc::strong_count(arc) > 1` is permanently
true at `interpreter_helpers/patterns.rs:331` and every push takes the
`Arc::make_mut` deep-copy branch.

Every generated encoder has exactly that shape:
`hc_enc_hir_module(w, …)` -> `hc_enc_hir_function(w, …)` -> `hc_enc_hir_block(w, …)`
-> … -> `w.put_i64(…)`. So the defect scaled with the module's encoded line
count, which is why it selected for the biggest files and looked like a
"lowering" cliff in the phase timings.

## Fix
`HirCodecWriter` (`src/compiler/20.hir/hir_codec_support.spl`) now accumulates
into bounded chunks: `parts` is the CURRENT chunk, capped at
`HIR_CODEC_CHUNK_LINES = 512`; a full chunk is joined once and moved to
`chunks`. The array that gets deep-cloned is therefore bounded, so each clone is
O(512) instead of O(n). `chunks` grows 512x more slowly, so its own residual
term is smaller by 512² (~262,000x).

Two shape details are deliberate:
- **The seal is inlined at each of the four `put_*` sites, not factored into a
  `me` helper.** A nested self-update method call is the exact shape whose
  mutation write-back the seed is documented to lose
  (`hir_phase_per_module_cost_2026-08-21.md`, fifth session).
- **Each `put_*` computes its line first and then does exactly ONE push +
  seal**, replacing the old early-`return` nil branches, so no path can skip the
  seal and let `parts` grow unbounded again.

Output is unchanged: `finish()` joins the same lines in the same order.

## Measurement (deployed seed, one tree, one binary, interpreted)

| module | encode before | encode after | blob |
|---|---|---|---|
| `src/compiler/50.mir/hwir/zca_rows.spl` | 1,139,353 ms | **6,702 ms** (170x) | 1,331,200 B both |
| `src/compiler/10.frontend/core/lexer_struct.spl` | 360,249 ms | **3,544 ms** (102x) | 539,375 B both |

The "before" rows are a true A/B on this same tree and binary: the pre-fix
algorithm was reproduced by setting `HIR_CODEC_CHUNK_LINES` to 100,000,000, i.e.
an unbounded `parts` — the writer then behaves exactly as it did before the
change. Lowering time is unchanged either side (zca_rows 8.6 s / 5.4 s;
lexer_struct 2.7 s both), which is the point: the cliff was never in lowering.

These two numbers also close the accounting against run12's `[build] hir`
receipts. lexer_struct: 74 s profiled lowering + ~360 s encode against a 925 s
completion `dt=` (the remainder is the shared, heavily-loaded 8-core box, where
run12 had many concurrent shard workers). zca_rows: 7.8 s lowering + ~1,139 s
encode against 1,543 s.

Byte-count identity across the change, plus the encode -> decode -> encode
byte-identity example in the spec, is the evidence that chunking changed no
output.

## Not fixed here: the seed interpreter defect that caused it
The compiler-side fix bounds the blast radius; it does not remove the underlying
rule. **Passing a class-typed value through more than one parameter hop makes
every subsequent `me`-method field-array mutation deep-clone that array.** Any
other builder/accumulator threaded through helper functions pays the same O(n²),
silently. The general fix is move-on-pass (or a steal) for class arguments so
`Arc::make_mut` sees a sole owner — the `STEAL_*` counters exist and are all
**0** for this shape, so the steal path is not merely failing, it is never
attempted. That is a semantic change to the interpreter's ownership model and is
deliberately NOT attempted in this lane. A census of other multi-hop accumulator
shapes across the compiler is owed.

## Pin
`test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl` (mirrored in
`test/unit/`) pins the ALGORITHM, not a wall clock:
- `parts` never exceeds `HIR_CODEC_CHUNK_LINES` — the bound that bounds the clone;
- `chunks.len() > 4` on the fixture, so the bound is actually reached and the
  first assertion is not vacuously true;
- encode cost for a 4x larger module stays under 8x (linear ~4x, quadratic ~16x)
  — a RATIO, so a faster machine cannot satisfy it and a slower one cannot break it;
- encode -> decode -> encode is byte-identical, so the chunk seam changes no byte.

Verified red by raising `HIR_CODEC_CHUNK_LINES` to 100,000,000 (an unbounded
writer, i.e. the pre-fix algorithm): the two mechanism examples FAIL and the
byte-identity example still passes — which is itself the cross-check that
chunking is output-neutral.

## Landing record: pre-existing test-tree divergence stepped over
`check-test-tree-divergence-delta.shs` returned
`PASS — 4 pre-existing offender(s), 0 introduced by this range` for
`b73b6073e66..<this commit>`. The guard is RED at the base
(`FAIL — 858 diverged vs 854 baselined (4 new, 0 fixed-but-still-baselined)`),
and per `.claude/rules/vcs.md` the scoped-delta escape requires the pre-existing
offender list to be recorded. The four NEW-vs-baseline offenders already present
at `origin/main` — none of them touched by this change — are:

    unit:app/llm_caret/agent_runtime_provider_spec.spl
    unit:compiler/hir/reexport_physical_cache_spec.spl
    unit:compiler/hir/resolve_import_symbols_spec.spl
    unit:compiler/semantics/collection_patterns_lint_spec.spl

The full 858-entry diverged list is what the helper writes to
`/mnt/data/tmp/test_tree_divergence_preexisting.txt`. This change introduces
zero divergence: the new spec is committed byte-identically to both
`test/01_unit/compiler/hir/` and `test/unit/compiler/hir/`.
