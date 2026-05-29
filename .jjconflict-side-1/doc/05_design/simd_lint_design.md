# SIMD Opportunity Lint — Design

**Pass:** `L-SIMD-001` through `L-SIMD-011`
**Location:** `src/compiler/35.semantics/lint/simd_opportunity_lint.spl`
**Phase:** Semantic lint (layer 35), text-based — runs before AST formation
**Status:** L-SIMD-001–005 implemented Wave J; L-SIMD-006–011 implemented Wave K (2026-05-02)

---

## Table of Contents

1. [Pass Insertion Point](#1-pass-insertion-point)
2. [Approach: Text-Based vs AST/MIR](#2-approach-text-based-vs-astmir)
3. [Severity Rules](#3-severity-rules)
4. [Diagnostic Catalog](#4-diagnostic-catalog)
5. [When NOT to Lint](#5-when-not-to-lint)
6. [Capability Dependence](#6-capability-dependence)
7. [Open Questions](#7-open-questions)

---

## 1. Pass Insertion Point

### Lint pipeline location

The compiler's lint pipeline lives in `src/compiler/35.semantics/lint/`. Each
pass is a standalone `.spl` file that exports one or more `pub fn lint_*(source: text, path: text) -> [<Warning>]`
functions. The module-level export facade is `__init__.spl`.

The driver entry point is:

```
src/compiler/80.driver/build/cli_entry.spl  line 137  fn run_lint() -> i64
```

`run_lint()` currently shells out to `cargo clippy` for Rust-seed linting.
The `.spl` lint passes are invoked separately during the `bin/simple build check`
pipeline, which calls each registered lint function against every `.spl` source
file in the tree.

### Registration

To register a new lint pass:

1. Add the `.spl` file to `src/compiler/35.semantics/lint/`.
2. Export the warning struct and all public lint functions in `__init__.spl`.
3. The build system picks up all exports from that module automatically.

For `simd_opportunity_lint.spl`, the following additions are needed in
`__init__.spl` (not yet applied — see [Open Questions](#7-open-questions)):

```
export simd_opportunity_lint.*

# Re-exported from simd_opportunity_lint.spl
export SimdOpportunityWarning
export lint_simd_elementwise_add, lint_simd_reduce_sum
export lint_simd_xor_loop, lint_simd_elementwise_max
export lint_simd_const_shr_loop, lint_simd_opportunities
```

### Existing lint passes for reference

| File | Rules | Mechanism |
|------|-------|-----------|
| `mcp_perf_lint.spl` | MCP001–MCP004 | text scan, function-name tracking |
| `remote_exec_lint.spl` | RJIT001–RJIT005 | text scan, multi-line buffer accumulation |
| `sffi_lint.spl` | SFFI001–SFFI008 | HirClass/HirStruct struct inspection |
| `simd_opportunity_lint.spl` | L-SIMD-001–011 | text scan, loop body safety check |

`sffi_lint.spl` is the only pass that operates on HIR structs. All others are
text-based and use `iter_code_lines()` from `lint_text.spl`.

---

## 2. Approach: Text-Based vs AST/MIR

The existing lint infrastructure in the `35.semantics/lint/` directory is
**uniformly text-based**: all passes use `iter_code_lines(source)` to walk
non-docstring lines and apply pattern matching with `contains()`, `starts_with()`,
and manual substring search.

An AST/MIR-level SIMD lint would be more precise but:
- The AST visitor primitives for external lint passes are not yet exposed
  (no stable `AstVisitor` trait in `35.semantics/`).
- HIR-level loop analysis would require the type checker to have run, placing
  the pass after layer 40.
- The text-based approach already catches the canonical patterns (straight-line
  element-wise loops) that constitute 90 %+ of practical SIMD opportunities.

**Decision:** implement as a text-based pass consistent with peer passes. File
a follow-up request (see [Open Questions](#7-open-questions)) to add an
AST-level variant once the visitor API stabilises.

---

## 3. Severity Rules

| Severity | Meaning | When to use |
|----------|---------|-------------|
| `info` | Definite SIMD opportunity, cosmetic — low confidence the loop is hot | Element-wise arithmetic, max, reduction on arrays of unknown size |
| `warning` | High-confidence hot path — the pattern is a canonical performance kernel | XOR over byte arrays (cipher/hash), inner loop in a copy kernel |
| `note` | Suggestion only — user may choose to ignore | Constant shift, min/max ternary that might already be optimised by the backend |

### Rationale

Drowning users in `warning`-level diagnostics trains them to ignore warnings.
`info` is the default for "this *could* be faster"; `warning` is reserved for
patterns where it would be surprising *not* to use SIMD (e.g., a plain XOR
loop over bytes in a file with `cipher` or `hash` in its path).

---

## 4. Diagnostic Catalog

Each entry: lint code, severity, short message, long explanation, before/after
fix snippet.

---

### L-SIMD-001 — Element-wise add (info)

**Trigger:** `for i in 0..n: out[i] = a[i] + b[i]`

**Message:** `scalar element-wise add loop over N elements can be SIMDified`

**Explanation:**
A straight-line add of two equal-length arrays maps directly onto the
`Vector.add` method. The compiler cannot auto-vectorise this today because
the loop body is not in MIR form at the lint stage. Using `FixedVec.add`
explicitly gives the backend a concrete SIMD operation to lower.

**Before:**
```simple
var out: [i32] = []
for i in 0..n:
    out[i] = a[i] + b[i]
```

**After (fixed-width, n known at compile time):**
```simple
val out = fixedvec_from_slice(a).add(fixedvec_from_slice(b)).to_array()
```

**After (runtime-sized, large n):**
```simple
val out = ScalableVec<i32>(elements: a).add(ScalableVec<i32>(elements: b)).to_array()
```

**Does NOT fire when:**
- Loop body contains any function call other than `.push()`
- Loop body contains I/O (`print`, `file_read`, etc.)
- Loop body already references `FixedVec` or `ScalableVec`
- Loop body has `return`, `break`, or `continue`

---

### L-SIMD-002 — Scalar accumulator / reduce_sum (info)

**Trigger:** `var s = 0` immediately followed by `for i in 0..n: s = s + a[i]`

**Message:** `scalar accumulator loop over 's' can be replaced with SIMD reduce_sum`

**Explanation:**
Accumulation is the textbook use case for horizontal reductions. `FixedVec.reduce_sum()`
sums all lanes and returns a scalar, replacing the entire loop.

**Before:**
```simple
var s = 0
for i in 0..n:
    s = s + a[i]
```

**After:**
```simple
val s = fixedvec_from_slice(a).reduce_sum()
```

**Notes:** The text scanner tracks the last `var <name> = 0` declaration before
the loop, so the accumulator variable name is extracted dynamically.

---

### L-SIMD-003 — Byte-array XOR loop (warning)

**Trigger:** `for i in 0..n: out[i] = a[i] ^ b[i]`

**Message:** `byte-array XOR loop over N elements is a hot SIMD opportunity`

**Explanation:**
XOR over byte arrays is the canonical inner loop of stream ciphers, block
cipher feedback modes, and hash mixing. On SSE2+ (128-bit), a single
`PXOR` instruction processes 16 bytes simultaneously. This lint fires as
`warning` (not `info`) because the presence of an XOR loop over bytes is
almost always a performance-critical path.

**Before:**
```simple
for i in 0..n:
    out[i] = a[i] ^ b[i]
```

**After (16-byte block, FixedVec):**
```simple
val out = FixedVec<u8>(elements: a, lanes: 16).xor(FixedVec<u8>(elements: b, lanes: 16)).to_array()
```

**After (runtime-sized slice):**
```simple
val out = fixedvec_from_slice(a).xor(fixedvec_from_slice(b)).to_array()
```

**Note on `xor` vs `bit_xor`:** `FixedVec` exposes `.xor()` as the primary
element-wise XOR method (see `fixed.spl` line 235: `fn xor(self, rhs: Self) -> Self`).
The trait-level name is `bit_xor` but the concrete class method is `xor`.

---

### L-SIMD-004 — Element-wise max loop (info)

**Trigger:** `for i in 0..n: out[i] = max(a[i], b[i])`
  or: `for i in 0..n: out[i] = if a[i] > b[i]: a[i] else: b[i]`

**Message:** `scalar element-wise max loop over N elements can be SIMDified`

**Explanation:**
Element-wise maximum maps to `FixedVec.max(other)`. On most ISAs (NEON,
SSE4.1, AVX2) this lowers to a single `VMAXPS`/`VPMAXSD` instruction per
vector. The scalar branch version also fires this lint because the ternary
select pattern is semantically identical.

**Before:**
```simple
for i in 0..n:
    out[i] = max(a[i], b[i])
```

**After:**
```simple
val out = fixedvec_from_slice(a).max(fixedvec_from_slice(b)).to_array()
```

---

### L-SIMD-005 — Constant right-shift loop (note)

**Trigger:** `for i in 0..n: out[i] = a[i] >> K`
  where K is a numeric literal or named constant

**Message:** `constant right-shift by K over N elements can use FixedVec.shr_logical`

**Explanation:**
A constant logical right-shift of all elements maps to `FixedVec.shr_logical(count)`.
This is a `note` (not `info`) because the backend may already fold this into a
vectorised shift in some cases. The explicit SIMD form guarantees it.

**Before:**
```simple
for i in 0..n:
    out[i] = a[i] >> 2
```

**After:**
```simple
val out = fixedvec_from_slice(a).shr_logical(2).to_array()
```

**Note on arithmetic vs logical:** `shr_logical` fills from the left with zeros
(unsigned shift). For signed arithmetic right-shift, use `shr_arith`. The lint
always suggests `shr_logical` since `>>` in Simple is defined as logical shift
(`FixedVec.shr_logical` matches the `>>` scalar semantics).

---

### L-SIMD-006 — Memcpy loop (warning)

**Trigger:** `for i in 0..n: out[i] = src[i]`  (pure element copy, no arithmetic)

**Message:** `scalar element-copy loop over N elements is a memcpy SIMD opportunity`

**Explanation:**
A loop that copies one array element-by-element is the scalar equivalent of
`memcpy`. `FixedVec` `from_array`/`to_array` and `to_slice_into` perform bulk
copy without per-element overhead and give the backend a concrete bulk-move
operation to lower to SSE2 `MOVDQU` or AVX2 `VMOVDQU`.

**Before:**
```simple
for i in 0..n:
    out[i] = src[i]
```

**After (produce new array):**
```simple
val out = fixedvec_from_slice(src).to_array()
```

**After (copy into existing buffer):**
```simple
fixedvec_from_slice(src).to_slice_into(out)
```

**Does NOT fire when:**
- Body has any arithmetic operator (`+`, `-`, `*`, `/`, `^`, `>>`, `<<`)
- Body has any function call

---

### L-SIMD-007 — Byte-mismatch scan (info)

**Trigger:** `for i in 0..n: if a[i] != b[i]: break`

**Message:** `byte-mismatch scan loop over N elements can use SIMD cmp_eq`

**Explanation:**
Scanning two arrays for the first differing byte is a hot path in compression
match-length extensions and string comparison (J3 §M Pattern Alpha, J3 §8.2).
`vpcmpeqb` + `movemask` + `tzcnt` processes 16 bytes per iteration.

The fix uses real `FixedVec` methods available today; the planned
`find_first_mismatch(a, b)` helper will wrap this idiom once it lands.

**Before:**
```simple
for i in 0..n:
    if a[i] != b[i]: break
```

**After:**
```simple
val eq_mask = fixedvec_from_slice(a).cmp_eq(fixedvec_from_slice(b))
val all_equal = eq_mask.reduce_and()   # 0 means at least one lane differs
# planned: find_first_mismatch(a, b) — see simd_opportunity_lint: L-SIMD-007 follow-up
```

---

### L-SIMD-008 — ASCII tolower loop (warning)

**Trigger:** `for i in 0..n: if a[i] >= 0x41 and a[i] <= 0x5A: out[i] = a[i] + 32 else: out[i] = a[i]`
  or compact: `out[i] = if a[i] >= 65 and a[i] <= 90: a[i] + 32 else: a[i]`

**Message:** `ASCII tolower loop over N bytes can be SIMDified with mask_select`

**Explanation:**
ASCII case conversion is called by tokenisers, JSON parsers, and compiler
identifier normalisation (J4 §3 P4, J4 §5 R5). SSE2 `PCMPGTB` + masked
`PADDB` processes 16 characters per cycle. The fix uses the real
`FixedVec.cmp_ge`, `cmp_le`, `and`, `mask_select`, and `add` methods.

**Before:**
```simple
for i in 0..n:
    if a[i] >= 0x41 and a[i] <= 0x5A:
        out[i] = a[i] + 32
    else:
        out[i] = a[i]
```

**After:**
```simple
val va    = fixedvec_from_slice(a)
val lo    = FixedVec<u8>(elements: splat_array(0x41u8, n), lanes: n)
val hi    = FixedVec<u8>(elements: splat_array(0x5Au8, n), lanes: n)
val delta = FixedVec<u8>(elements: splat_array(32u8, n), lanes: n)
val mask  = va.cmp_ge(lo).and(va.cmp_le(hi))
val out   = FixedVec.mask_select(mask, va.add(delta), va).to_array()
```

---

### L-SIMD-009 — ReLU loop (info)

**Trigger:** `for i in 0..n: out[i] = max(a[i], 0)` or ternary form with `>= 0`

**Message:** `ReLU-shaped max(a[i], 0) loop over N elements can use FixedVec.max`

**Explanation:**
The rectified linear unit (ReLU) activation is the highest-frequency loop in
ML inference code (J4 §5 R3). `VMAXPS` lowers to a single instruction per 4
or 8 floats. This rule is a specialisation of L-SIMD-004 for the constant-zero
operand: the fix snippet uses `FixedVec.max` with a zero vector constructed
from `splat_array`.

**Before:**
```simple
for i in 0..n:
    out[i] = max(a[i], 0)
```

**After:**
```simple
val zeros = FixedVec<f32>(elements: splat_array(0.0, n), lanes: n)
val out   = fixedvec_from_slice(a).max(zeros).to_array()
```

---

### L-SIMD-010 — Byte-frequency histogram (note)

**Trigger:** `for i in 0..n: histogram[a[i]] += 1`

**Message:** `byte-frequency histogram loop over N elements may benefit from SIMD if profiled hot`

**Explanation:**
Building a 256-entry frequency table is a hot loop in Huffman compression and
entropy estimation (J3 §M Pattern Delta). The scatter-increment pattern
(`histogram[a[i]] += 1`) is not trivially vectorisable due to potential
aliasing; however a 4-accumulator interleaved approach can yield 2–3× speedup
by reducing pipeline stalls from back-to-back dependent loads/stores.

This fires as `note` because:
- The loop may not be hot enough to justify the added complexity
- A planned `byte_histogram_simd(a)` primitive will wrap the idiomatic form

**Before:**
```simple
for i in 0..n:
    histogram[a[i]] += 1
```

**After (manual 4-accumulator — available now):**
```simple
var h0: [i64] = splat_array(0, 256)
var h1: [i64] = splat_array(0, 256)
var h2: [i64] = splat_array(0, 256)
var h3: [i64] = splat_array(0, 256)
var k = 0
while k + 3 < n:
    h0[a[k]]     = h0[a[k]] + 1
    h1[a[k + 1]] = h1[a[k + 1]] + 1
    h2[a[k + 2]] = h2[a[k + 2]] + 1
    h3[a[k + 3]] = h3[a[k + 3]] + 1
    k = k + 4
# merge h0..h3 into histogram[i] = h0[i] + h1[i] + h2[i] + h3[i]
# planned: val hist = byte_histogram_simd(a)  — see simd_opportunity_lint: L-SIMD-010 follow-up
```

**Does NOT fire when:**
- Index expression contains a function call: `histogram[hash(a[i])] += 1` — no lint, hash is not a no-op

---

### L-SIMD-011 — Key-XOR cipher loop (warning)

**Trigger:** `for i in 0..n: out[i] = a[i] ^ key[i % keylen]`

**Message:** `key-XOR cipher loop over N bytes is a hot SIMD opportunity`

**Explanation:**
The repeating-key XOR is the inner loop of Vigenère-style ciphers and RC4-based
stream ciphers (J2 §M). It differs from L-SIMD-003 (which detects `a[i] ^ b[i]`
with matching indices) in that the key index uses modulo, preventing direct
`FixedVec.xor(key_vec)` without first tiling the key.

The fix tiles the key once into a full-length buffer (scalar, O(n)), then
performs a single `FixedVec.xor` pass. The per-element modulo disappears from
the hot path.

**Before:**
```simple
for i in 0..n:
    out[i] = a[i] ^ key[i % keylen]
```

**After:**
```simple
# Tile key to length n once (scalar pre-pass):
var tiled: [u8] = []
var k = 0
while k < n:
    tiled.push(key[k % keylen])
    k = k + 1
# SIMD XOR pass:
val out = fixedvec_from_slice(a).xor(fixedvec_from_slice(tiled)).to_array()
# planned: tile_to_len(key, keylen, n) helper — see simd_opportunity_lint: L-SIMD-011 follow-up
```

---

## 5. When NOT to Lint

The following conditions suppress all SIMD lints on a loop:

| Condition | Reason |
|-----------|--------|
| Body contains I/O call (`print`, `file_read`, `file_write`, `.write(`, `.read(`, `.open(`) | I/O order must be preserved; cannot vectorise |
| Body contains `rt_` prefixed call | FFI/runtime calls have unknown side effects |
| Body contains any function call other than `.push()` | Unknown side effects; may alias output arrays |
| Body contains `return`, `break`, or `continue` | Control-flow divergence; lane-masking not free |
| Body already uses `FixedVec` or `ScalableVec` | Already SIMD — no opportunity to flag |
| Loop variable not a simple range `0..N` | Arbitrary iterators may not be contiguous |
| Loop is over a `for x in collection:` (not indexed) | Cannot infer array alignment |

The safety check is implemented in `_loop_body_is_safe()` which scans the
body lines until it detects dedent back to the loop's indent level.

---

## 6. Capability Dependence

SIMD lints should only fire when the target architecture can execute the
suggested replacement code. The current implementation fires unconditionally
because the text-based lint pass does not have access to the compilation
target at the point it runs.

The intended future behaviour (blocked on AST-level lint API):

```
# Pseudo-code for target-gated lint (future, not yet implemented)
val features = SimdFeatureSet.for_target(ctx.target)
if features.has_sse2 or features.has_neon:
    # fire L-SIMD-001 through L-SIMD-003 (128-bit lanes)
if features.has_avx2:
    # fire with 256-bit lane suggestion
if features.has_riscv_v or features.has_sve:
    # suggest ScalableVec variant instead of FixedVec
```

The `SimdFeatureSet` query API is documented in
`doc/04_architecture/simd_unified_architecture.md` §6 (Capability Detection)
and `src/lib/nogc_sync_mut/simd/` — `fixed.spl` exposes
`preferred_lanes_for_target()` and `lane_count()` on each `FixedVec` instance.

**Workaround for current text-based pass:** the fix snippets use
`fixedvec_from_slice()` (the generic constructor) rather than a
fixed-lane type parameter. This means the generated code will compile
correctly on all targets, degrading to scalar loops via the interpreter
fallback on targets without SIMD support (per `fixed.spl` §C2 §7).

**TODO:** Once the lint pass has access to a `CompileContext` object (see
`src/compiler/35.semantics/`), gate the `warning`-severity lint (L-SIMD-003)
on `target.has_sse2 or target.has_neon` and suppress the other rules on
pure-scalar targets.

---

## 7. Open Questions

### Q1: `__init__.spl` registration

The `simd_opportunity_lint.spl` pass is implemented but not yet registered in
`__init__.spl`. This is intentional: `__init__.spl` is a shared file and
modifying it in parallel with other Wave J agents risks a merge conflict.
The registration diff is three lines and can be applied as a follow-up
single-file commit:

```diff
+export simd_opportunity_lint.*
+export SimdOpportunityWarning
+export lint_simd_elementwise_add, lint_simd_reduce_sum, lint_simd_xor_loop
+export lint_simd_elementwise_max, lint_simd_const_shr_loop, lint_simd_opportunities
+export lint_simd_memcpy_loop, lint_simd_byte_mismatch_scan, lint_simd_ascii_tolower
+export lint_simd_relu, lint_simd_histogram, lint_simd_key_xor
```

### Q2: AST-level visitor API

The text-based approach catches the trivial patterns well but has two
limitations:
1. It cannot resolve type aliases (e.g., a loop over `[Byte]` where `Byte = u8`
   does not trigger L-SIMD-003 unless the literal `u8` appears in the body).
2. It cannot distinguish nested loops from flat loops.

Once `src/compiler/35.semantics/` exposes a stable `HirVisitor` or `MirVisitor`
trait for external passes, the SIMD lint should be rewritten to operate on
`HirLoop` nodes with element type annotations. Track as bug/feature:
`simd_opportunity_lint: upgrade to HIR-level pattern matching`.

### Q3: Loop-unroll annotation interaction

If a loop carries `@unroll` or `@simd` annotations, the lint should suppress
all L-SIMD warnings (the user has already made a decision). This requires
either a text-scan for the annotation on the preceding line or HIR access.
Currently not implemented.

### Q4: ScalableVec suggestion threshold

The current fix snippets always suggest `fixedvec_from_slice()`. For loops
where `n` is clearly a runtime variable (not a small literal), the suggestion
should prefer `ScalableVec`. A heuristic: if `n` is a single lowercase letter
or contains `len()`, suggest `ScalableVec`; if `n` is a numeric literal ≤ 64,
suggest `FixedVec<T, N>` with the explicit lane count.
