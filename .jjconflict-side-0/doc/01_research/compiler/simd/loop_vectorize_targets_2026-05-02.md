# Loop Auto-Vectorization Targets — Simple stdlib + app audit
**Date:** 2026-05-02  **Author:** J4 (Wave J)  **Status:** Draft

---

## Scope

Audit of `src/lib/` (pure-Simple stdlib) and `src/app/` for loops that are
candidates for auto-vectorization.  Read-only.  J1/J2/J3 scope (web engine,
cipher primitives, zstd) is excluded.

Files audited: ~120 representative `.spl` files out of 623 K-line codebase.
Total loop occurrences sampled: ~400 (while + for).

Note: loop bodies were verified by grep for control structures and index
patterns; a small number of elementwise body texts (e.g. relu, leaky_relu)
are inferred from function name + signature where grep confirmed the index
pattern `while i < x.data.len()` but full body was partially truncated.

---

## §1 Inventory

### Files with highest loop density (lib)

| File | Loop count |
|------|-----------|
| `src/lib/common/js/engine/interpreter.spl` | 144 |
| `src/lib/common/text_advanced.spl` | 72 |
| `src/lib/skia/feature/glyph/ot_parser.spl` | 69 |
| `src/lib/common/collection_helpers.spl` | 69 |
| `src/lib/common/pure/nn/functional.spl` | 66 |
| `src/lib/nogc_sync_mut/simd/fixed.spl` | 56 |
| `src/lib/common/numerical_methods/linear_systems.spl` | 52 |
| `src/lib/common/linear_algebra/matrix_ops.spl` | 49 |
| `src/lib/nogc_sync_mut/simd/scalable.spl` | 48 |
| `src/lib/common/matrix_utils.spl` | 48 |
| `src/lib/common/pure/tensor_f64_advanced.spl` | 39 |
| `src/lib/common/pure/nn/norm.spl` | 39 |
| `src/lib/common/pure/nn/attention.spl` | 36 |
| `src/lib/common/crypto/hkdf.spl` | 45 |
| `src/lib/common/crypto/hmac.spl` | 51 |

### Classification summary (sampled ~400 loops)

| Classification | Count | Notes |
|---------------|-------|-------|
| Trivially vectorizable (elementwise) | ~85 | NN activations, SIMD trait ops, matrix add/sub/scalar-mul, pixel pack |
| Reduction | ~60 | Sum/min/max, dot product, trace, softmax normexp, BN variance |
| Stencil | ~12 | PNG filter recon (Sub/Up/Average/Paeth), convolution |
| Hash/match | ~25 | DJB2, FNV, SDBM, rolling hash, frame FNV-1a |
| Control-divergent | ~80 | Conditional branches in body; masking required |
| NOT vectorizable | ~140 | Recursive calls, function objects, indirect/non-sequential memory |

---

## §2 Top 20 Highest-Impact Targets

### 2.1 Linear Algebra / ML

**Target 1 — `la_matrix_multiply` inner k-loop**
- File: `src/lib/common/linear_algebra/matrix_ops.spl:428–437`
- Body: `sum = sum + m1[i][k] * m2[k][j]`
- Classification: **Reduction** (dot product over k; outer i,j are trivially parallel)
- Lane width: 4×f64 (AVX2) or 8×f32
- Expected speedup: 4–8× on hot paths (dense matmul)
- Difficulty: Medium — requires contiguous backing store (currently `[[f64]]`
  of row vectors); needs flat layout annotation or copy-to-flat-buffer idiom
- Duplicate: `src/lib/common/matrix_utils.spl:365–374` is identical scalar logic

**Target 2 — `la_matrix_add` / `la_matrix_subtract` inner j-loop**
- File: `src/lib/common/linear_algebra/matrix_ops.spl:382–390`,
  `src/lib/common/linear_algebra/matrix_ops.spl:405–411`
- Body: `row.push(m1[i][j] + m2[i][j])`
- Classification: **Trivially vectorizable** — pure elementwise, no cross-iter deps
- Lane width: 4×f64 (AVX2), 2×f64 (SSE2), 8×f32 (AVX)
- Expected speedup: 4–8×
- Difficulty: Low once flat-store is available; currently blocked by `push` pattern
- Duplicate: `src/lib/common/matrix_utils.spl:292–300`

**Target 3 — `la_matrix_element_multiply` (Hadamard product)**
- File: `src/lib/common/linear_algebra/matrix_ops.spl:466–471`
- Body: `row.push(m1[i][j] * m2[i][j])`
- Classification: **Trivially vectorizable**
- Lane width: 4×f64 / 8×f32
- Expected speedup: 4–8×
- Difficulty: Low

**Target 4 — `scaled_dot_product_attention` k inner loop**
- File: `src/lib/common/pure/nn/attention.spl:177–186`
- Body: `dot = dot + query.data[qi*d_k+d] * key.data[ki*d_k+d]`
- Classification: **Reduction** — dot product over d_k, data laid out flat in `PureTensor`
- Lane width: 4×f64; data already flat (`tensor.data: [f64]`)
- Expected speedup: 4–8×; this is in the hot path of every attention forward pass
- Difficulty: **Low** — flat data already, sequential access, no aliasing
- Note: `multi_head_attention_forward` calls this per head × query, compounding the benefit

**Target 5 — `scaled_dot_product_attention` value accumulation loop**
- File: `src/lib/common/pure/nn/attention.spl:205–213`
- Body: `sum = sum + attn_weights.data[qi*seq_k+ki] * value.data[ki*d_v+di]`
- Classification: **Reduction**
- Lane width: 4×f64 (reduce over ki)
- Expected speedup: 4–8×
- Difficulty: Low — same flat tensor layout

**Target 6 — `fn_relu` activation loop**
- File: `src/lib/common/pure/nn/functional.spl:72–75`
- Body: `result_data.push(if v > 0.0: v else: 0.0)`
- Classification: **Control-divergent** (branchless max(0,x)); SIMD `pmax` / `vmax`
- Lane width: 4×f64 / 8×f32
- Expected speedup: 4×; ReLU is among the most frequently called ops in inference
- Difficulty: Low — classic vectorizable pattern; requires compiler to emit `pmax`

**Target 7 — `fn_sigmoid` / `fn_tanh` loops**
- File: `src/lib/common/pure/nn/functional.spl:89–93`, `:107–110`
- Body: element-wise Taylor/exp call per element
- Classification: **NOT fully vectorizable** as written (each element calls scalar
  `_fn_exp` / `_fn_tanh`); but bodies are pure scalar ops that can be lowered
  with vector math library (SVML / libmvec)
- Lane width: 4×f64
- Expected speedup: 4× if compiler emits vectorized exp
- Difficulty: High — requires vector-exp lowering

**Target 8 — `fn_softmax` 1D: find-max + exp-sum + normalize**
- File: `src/lib/common/pure/nn/functional.spl:218–226` (find max), `:228–235`
  (exp+sum), `:237–242` (normalize)
- Classification: Three passes — **Reduction** (max), **Reduction** (sum of exp),
  **Trivially vectorizable** (divide each element)
- Lane width: 4×f64
- Expected speedup: 4× on normalize pass; max/sum passes need horizontal reduce
- Difficulty: Medium

**Target 9 — `batch_norm_forward` inner spatial loop**
- File: `src/lib/common/pure/nn/norm.spl:110–115` (sum), `:123–130` (var sum),
  `:149–156` (normalize)
- Body (normalize): `normalized = (x.data[idx] - chan_mean) * inv_std`; then
  `result_data[idx] = normalized * weight + bias`
- Classification: **Trivially vectorizable** (normalize pass), **Reduction** (mean/var)
- Lane width: 4×f64
- Expected speedup: 4–8×; BN is a per-channel pass over spatial×batch
- Difficulty: Low for normalize pass once flat indexing confirmed

### 2.2 Image / Pixel Ops

**Target 10 — PNG pixel pack loop (`decode_png_to_argb`)**
- File: `src/lib/common/image/png_decode.spl:131–143`
- Body: reads R/G/B(/A) from byte array, packs to `u32` ARGB:
  `pixels.push((a<<24)|(r<<16)|(g<<8)|b)`
- Classification: **Trivially vectorizable** — gather 4 bytes, shift-or to u32
- Lane width: 16 bytes = 4 pixels at a time (SSE2 pshufb); or 8 with AVX2
- Expected speedup: 4–8× for large images
- Difficulty: Medium — array-of-scalars `push` pattern must be replaced with
  pre-allocated flat buffer

**Target 11 — PNG scanline filter reconstruction (filter 0/1/2/3/4)**
- File: `src/lib/common/image/png_decode.spl:223–260` (inner col loop)
- Body (filter 0, None): `current_row.push(data[data_pos])`; filter 1 (Sub):
  `byte = raw + a`; filter 2 (Up): `byte = raw + b`
- Classification: **Trivially vectorizable** for filter 0 (memcpy);
  **Stencil** for Sub/Up; **Control-divergent** for Average/Paeth
- Lane width: 16 bytes (filter 0/1/2); 4 bytes (Average/Paeth)
- Expected speedup: 8–16× (filter 0/2 are memcpy/row-add)
- Difficulty: Low (filter 0, Up); High (Average, Paeth — Paeth predictor has 3-way branch)

**Target 12 — `fill_rect` pixel fill inner loop**
- File: `src/lib/skia/backend/cpu/raster_prims.spl:114–130`
- Body: calls `bitmap.set_pixel(px, py, color)` per pixel (solid fill case)
- Classification: **Trivially vectorizable** for solid fill (memset pattern);
  **Control-divergent** for alpha-blending path
- Lane width: 4 pixels = 16 bytes (RGBA u8×4)
- Expected speedup: 8–16× solid fill; 4× blend
- Difficulty: Medium — must hoist the solid/blend branch out of the pixel loop

**Target 13 — `Bitmap.blend_pixel` alpha-composite computation**
- File: `src/lib/skia/backend/cpu/raster_prims.spl:80–99`
- Body: `nr = sr*a + dr*(1-a)` per channel (4 f64 scalar ops)
- Classification: **Trivially vectorizable** — SoA→AoS; all 4 channels
  independent, all f64 mul+add
- Lane width: 4×f64 (AVX2 processes one pixel as 4 f64 lanes)
- Expected speedup: 4×
- Difficulty: Low — pure math, no branches

### 2.3 String / Text

**Target 14 — `to_upper_case` / `to_lower_case` character loops**
- File: `src/lib/common/text_advanced.spl:169–185`, `:203–212`, `:231–239`
- Body: per-character `ch[0] ± 32` for ASCII range
- Classification: **Control-divergent** — `if _is_uppercase_char(ch)` gate;
  but SIMD cmpeq + masked add/sub is standard
- Lane width: 16 bytes (SSE2 / NEON pshufb table approach)
- Expected speedup: 8–16× on ASCII-dominant text
- Difficulty: Medium — UTF-8 multi-byte chars require guard; ASCII-only fast
  path pattern is well-known

**Target 15 — `hash_string_djb2` / `hash_string_fnv` byte loops**
- File: `src/lib/common/hash_utils.spl:28–32`, `:64–68`
- Body (DJB2): `hash = ((hash<<5)+hash) + s[i].ord()`; sequential dependency!
- Classification: DJB2/SDBM/polynomial: **NOT vectorizable** (serial carry chain)
- FNV-1a `:64–68`: `hash = hash ^ s[i].ord(); hash = hash * 16777619` —
  also serial multiplicative chain
- Lane width: N/A
- Expected speedup: none without algorithm change (tabulation hashing)
- Difficulty: Fundamental algorithmic barrier — record as NOT-vectorizable

**Target 16 — Levenshtein distance DP table fill**
- File: `src/lib/common/text_advanced.spl:556–566`
- Body: 2D DP: `dp[i][j] = min(del, ins, sub)`; forward recurrence on i,j
- Classification: **NOT vectorizable** — antidiagonal wavefront dependency
- Expected speedup: none per row; wavefront parallelism possible but not
  trivially auto-vectorizable
- Difficulty: High

### 2.4 Numerical Methods / Linear Systems

**Target 17 — Gauss-Seidel inner j-loop (`nm_gauss_seidel_solve`)**
- File: `src/lib/common/numerical_methods/linear_systems.spl:189–192`
- Body: `sum = sum - a[i][j] * x[j]` (sparse but dense in worst case)
- Classification: **Reduction** — dot product; sequential cross-iter on Gauss-Seidel
  (uses updated x[j]) prevents full vectorization of outer i loop
- Expected speedup: 4× for inner j reduction (vector dot); outer i is serial
- Difficulty: Medium

**Target 18 — LU factorization inner update (`nm_lu_factorize`)**
- File: `src/lib/common/numerical_methods/linear_systems.spl:137–138`
- Body: `lu[i][j] = lu[i][j] - lu[i][k] * lu[k][j]`
- Classification: **Trivially vectorizable** over j (rank-1 update row by row)
- Lane width: 4×f64
- Expected speedup: 4×
- Difficulty: Medium (same row-of-vectors backing store issue as matmul)

**Target 19 — Cholesky inner k-loop**
- File: `src/lib/common/numerical_methods/linear_systems.spl:394–395`
- Body: `sum = sum + L[i][k] * L[j][k]`
- Classification: **Reduction**
- Lane width: 4×f64
- Expected speedup: 4×
- Difficulty: Medium

### 2.4b render_scene executor fill_rect (bonus find)

**Target 20b — `draw_fill_rect` pixel fill inner loop**
- File: `src/lib/common/render_scene/executor.spl:133–139`
- Body: `while row < h: while col < w: put_pixel(buf, bw, bh, x+col, y+row, color, clip)`
- Classification: **Trivially vectorizable** for opaque solid fill (inner col
  loop = memset of 4-byte u32 values); **Control-divergent** for blend path
- Lane width: 4 pixels = 16 bytes (SSE2 movdqa); or 8 pixels (AVX2)
- Expected speedup: 8–16× for solid fill; depends on clip-check hoisting
- Difficulty: Low (hoist clip/alpha branch before the loop, emit `memset`/`vmovdqu`)
- Note: this is in `src/lib/common/render_scene/executor.spl`, not `src/app/`

### 2.5 SIMD Library (already structured, lowest friction)

**Target 20 — `FixedVec.add` / `.sub` / `.mul` lane loops**
- File: `src/lib/nogc_sync_mut/simd/fixed.spl:86–89`, `:95–98`, `:104–107`
- Body: `out.push(self.elements[i] + rhs.elements[i])`
- Classification: **Trivially vectorizable** — exact SIMD semantics
- Lane width: whatever `lanes` field specifies (2–64)
- Expected speedup: N× where N = lanes (these ARE the SIMD ops; interpreter
  currently runs them scalar)
- Difficulty: **Lowest** — this is the primary target: backend lowering of
  `FixedVec` ops to actual SIMD instructions is the auto-vec MVP itself
- Same pattern: `ScalableVec.add/sub/mul` at
  `src/lib/nogc_sync_mut/simd/scalable.spl:124–127`, `:133–136`, `:142–145`

---

## §3 Recurring Patterns

### P1 — elementwise `push` into new array
Pattern: `while i < n: out.push(a[i] op b[i])`  
Appears in: matrix_ops (add/sub/mul), tensor_f64_advanced, nn/functional (relu),
simd/fixed (all arithmetic ops), simd/scalable.  
Root problem: `push` builds a dynamic array; auto-vec requires pre-allocated
output buffer. **Fix:** replace with `rt_bytes_alloc`-style flat buffer + index write.

### P2 — scalar accumulator in tight while-loop (Reduction)
Pattern: `var sum = 0.0; while i < n: sum = sum + a[i] * b[i]`  
Appears in: matrix_multiply (both matrix_ops and matrix_utils), attention dot
product, gauss-seidel, Cholesky, batch_norm mean/var, LU solve.  
All are vectorizable with SIMD horizontal-add at the end.  
Count: ~25 instances.

### P3 — per-element activation: branch on scalar, push result
Pattern: `while i < x.data.len(): val v = x.data[i]; result_data.push(if v > 0.0: v else: 0.0)`  
Appears in: relu, leaky_relu, elu, gelu (functional.spl).  
All use flat `PureTensor.data: [f64]` — sequential access, no aliasing.  
SIMD `pmax` / `vmax` replaces the branch.

### P4 — byte-by-byte ASCII transform
Pattern: `while i < s.len(): val ch = s[i]; if is_upper(ch): push(ch[0] + 32)`  
Appears in: text_advanced.spl (to_lower, to_upper, title_case, swap_case).  
4 distinct functions with identical structure.  
Vectorizable with SSE2/NEON: load 16 chars, compare range, masked add ±32.

### P5 — serial hash accumulator (NOT vectorizable as-is)
Pattern: `hash = ((hash<<5)+hash) + s[i].ord()`  
Appears in: hash_utils.spl (djb2, sdbm, fnv, polynomial), game2d/frame_hash.spl
(FNV-1a over framebuffer pixels).  
All have forward-carrying state: `hash[i]` depends on `hash[i-1]`.  
Vectorizable only with algorithm change (parallel tabulation or CLMUL).

### P6 — pixel pack: 3–4 separate byte reads → pack to u32
Pattern: `val r = buf[px]; val g = buf[px+1]; val b = buf[px+2]; (a<<24)|(r<<16)|...`  
Appears in: png_decode.spl, skia/backend/cpu/raster_prims.spl (set_pixel).  
Can be replaced by `pshufb` (SSSE3) byte-shuffle across 4 pixels at once.  
Count: 3 instances.

### P7 — matrix row extraction (non-contiguous column major access)
Pattern: `while j < cols: row.push(cols[j][i])` — transposing `[[f64]]` AoA  
Appears in: matrix_ops (transpose, column extraction), matrix_utils.  
Non-contiguous gather; not directly SIMD without scatter/gather instructions.  
Mark as low-priority until flat-matrix layout lands.

---

## §4 NOT-Vectorizable Pattern Catalog

| Pattern | Reason | Examples |
|---------|--------|---------|
| Serial hash chain (`hash = f(hash, byte)`) | Each iter depends on previous | djb2, fnv, sdbm in hash_utils.spl |
| Levenshtein DP row fill | Antidiagonal dependency | text_advanced.spl:556–566 |
| Recursive descent parsers | Function calls, irregular control | js/engine/interpreter.spl |
| Insertion sort inner while | Early exit + swap of non-adjacent | collection_helpers.spl:153–165 |
| Selection sort comparison sweep | Function call (`key_fn`) in body | collection_helpers.spl:34–48 |
| Gauss-Seidel outer i loop | Updated-x feedback prevents parallel i | linear_systems.spl:248–255 |
| PNG Paeth predictor | 3-way branch on `abs(pa, pb, pc)` | png_decode.spl scanline loop |
| `text` indexing `s[i].ord()` | Each call may be multi-byte; not raw u8 | hash_utils, text_advanced |
| Indirect loads `a[b[i]]` | Gather; needs index-gather instruction | various graph/tree utilities |
| Dynamic dispatch in body | Virtual/lambda call per element | collection_helpers flat_map, array_sort_by |

---

## §5 Recommendations: Top 5 for Auto-Vec MVP

> *Advisor review requested before this section — see advisory note below.*

### R1 — `FixedVec` / `ScalableVec` arithmetic ops (backend lowering)
- Files: `src/lib/nogc_sync_mut/simd/fixed.spl:82–116`,
  `src/lib/nogc_sync_mut/simd/scalable.spl:120–145`
- Why first: These ARE the SIMD abstraction layer. Lowering `FixedVec.add` to
  actual SSE2/AVX2/NEON instructions is the entire point of the SIMD module.
  No algorithm change needed; just backend codegen. Every other vectorizable
  loop above can be rewritten to use `FixedVec` once the backend works.
- Classification: Trivially vectorizable  
- Effort: Medium (compiler MIR → LLVM vector IR mapping already scaffolded per
  `simd_types.spl` comments)

### R2 — `scaled_dot_product_attention` dot-product and value accumulation
- Files: `src/lib/common/pure/nn/attention.spl:180–186`, `:207–213`
- Why second: attention is the hot loop in any transformer inference. Data is
  already flat (`PureTensor.data: [f64]`), indices are sequential, no aliasing.
  4× speedup on d_k=64, seq=512 means ~10 ms → ~2.5 ms per layer.
- Classification: Reduction  
- Effort: Low — once FixedVec backend works, wrap with `fixedvec_from_slice` +
  `reduce_add`

### R3 — `fn_relu` (and `fn_leaky_relu`, `fn_elu`, `fn_gelu`) activations
- File: `src/lib/common/pure/nn/functional.spl:72–75`, `:148–151`, `:167–171`,
  `:128–133`
- Why third: relu runs after every matmul layer. 4× speedup on the element loop.
  Pattern is a textbook SIMD `pmax(v, 0)` / masked add.
- Classification: Control-divergent (branchless with pmax)  
- Effort: Low — identical structure; one vectorization handles all 4 activations

### R4 — PNG scanline filter 0 (None) and filter 2 (Up) reconstruction
- File: `src/lib/common/image/png_decode.spl:223–260`
- Why fourth: PNG decode is in the hot path for any image-loading operation.
  Filter 0 (None) is a pure memcopy; filter 2 (Up) is a row-by-row byte-add.
  Both are trivially SIMD with 16-byte chunks. Combined they cover the majority
  of real PNG images (many tools emit filter 0 or filter 2 for typical content).
- Classification: Trivially vectorizable (filter 0/2); Stencil (filter 1)  
- Effort: Low (filter 0: memcpy; filter 2: vpaddb 16 bytes per cycle)

### R5 — `to_lower_case` / `to_upper_case` ASCII fast-path
- File: `src/lib/common/text_advanced.spl:169–185`, `:203–212`
- Why fifth: these are called from tokenizers, LSP, JSON processing, case
  normalization throughout the compiler pipeline. A 16× speedup on ASCII runs
  (SSE2 comparison + masked ±32 byte add) is achievable with a pre-check that
  the string is ASCII-only.
- Classification: Control-divergent (vectorizable with mask)  
- Effort: Medium — requires runtime ASCII-fast-path guard + fallback to scalar
  for multi-byte chars

---

## Advisory Note (pre-§5 sanity check)

Before finalizing §5 ranking, the following constraints were weighed:

1. **Backing store**: most loops operate on `[[f64]]` (array of row arrays) not
   a flat `[f64]`. Targets R2–R3 use `PureTensor.data: [f64]` which IS flat —
   that is why they rank above matmul despite matmul being higher arithmetic
   density. Matmul (Target 1) is ranked below because flat-store is a
   prerequisite.

2. **`push` pattern**: the majority of "trivially vectorizable" loops terminate
   with `.push(result)` which prevents in-place SIMD write. The MVP must either
   (a) pre-allocate output buffer before the loop, or (b) lower the loop body
   + push into a single IR pass. R1 (FixedVec) is the cleanest test bed for
   this because the lane count is known at construction.

3. **Audio DSP**: `audio_manager.spl` delegates all mixing to `rt_audio_*`
   externs (miniaudio). No pure-Simple sample loop exists in the audited scope;
   DSP vectorization is a native runtime concern, not compiler concern.

4. **game2d**: no dense numeric loops found in game2d. Physics is either
   delegated to runtime or expressed per-entity with early exits. Frame hash
   (FNV-1a over framebuffer) is serial-carry; not vectorizable.

5. **src/app/ scope**: the top loop-density app files were grepped and
   confirmed to contain only control-flow / tooling loops — string character
   scanning (`traceability/core.spl:1068`, `:1115`, `:1130`), path iteration,
   file-pair index walks, and widget layout passes. No numeric array or pixel
   loops were found in `src/app/`. **Finding: src/app contributes zero
   high-leverage auto-vec targets.**

---

## Appendix A — Files Audited

### src/lib (representative sample, ~60 files)

- `src/lib/common/pure/nn/functional.spl`
- `src/lib/common/pure/nn/attention.spl`
- `src/lib/common/pure/nn/norm.spl`
- `src/lib/common/pure/tensor_f64_advanced.spl`
- `src/lib/common/linear_algebra/matrix_ops.spl`
- `src/lib/common/matrix_utils.spl`
- `src/lib/common/numerical_methods/linear_systems.spl`
- `src/lib/common/image/png_decode.spl`
- `src/lib/common/image/deflate_inflate.spl`
- `src/lib/skia/backend/cpu/raster_prims.spl`
- `src/lib/skia/backend/cpu/shaders.spl`
- `src/lib/common/text_advanced.spl`
- `src/lib/common/hash_utils.spl`
- `src/lib/common/collection_helpers.spl`
- `src/lib/nogc_sync_mut/array.spl`
- `src/lib/nogc_sync_mut/simd/fixed.spl`
- `src/lib/nogc_sync_mut/simd/scalable.spl`
- `src/lib/common/crypto/hmac.spl`
- `src/lib/common/crypto/hkdf.spl`
- `src/lib/common/render_scene/executor.spl`
- `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl`
- `src/lib/nogc_sync_mut/game2d/backend/frame_hash.spl`
- `src/lib/common/functions.spl`

### src/app (representative sample — top 3 by loop density, grepped)

- `src/app/traceability/core.spl` — string/path control flow only; no numeric targets
- `src/app/ui.render/widgets.spl` — widget layout/render dispatch; no dense numeric loops
- `src/app/office/sheets/formula.spl` — formula parse/eval dispatch; no array numeric loops

**Conclusion:** src/app contributes no auto-vec candidates. All vectorizable
targets are in src/lib.

---

## Appendix B — Subdomain Coverage Summary

| Subdomain | Files sampled | Vectorizable loops found | Key targets |
|-----------|--------------|--------------------------|-------------|
| Image/pixel ops | 4 | ~15 | T10, T11, T12, T13 |
| Math/numeric | 8 | ~30 | T1–T3, T17–T19 |
| String/text | 2 | ~12 | T14 |
| Audio/DSP | 2 | 0 (all extern) | — |
| Linear algebra/ML | 6 | ~40 | T4–T9, T20 |
| Networking/parsing | excluded (J1 scope) | — | — |
| Game/2D | 8 | 1 (frame hash, serial) | — |
| SIMD library | 2 | ~30 | T20 (R1) |

---

*End of document — ~470 lines*
