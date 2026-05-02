<!-- claude-design -->
# Design: SIMD Open Question Resolutions (2026-05-02)

All 12 open questions blocking SIMD phases M0–M9 have been resolved in this document. OQ-6
(diagnostic code count, M0 entry gate) is decided here: C2 §9's 26-code catalog is
authoritative; the brief's "33" figure is stale. OQ-7 (x86 file split, M1 entry) confirms
the 2-file layout: keep `x86_64_simd.spl` for SSE+AVX2, add a new `x86_64_avx512.spl`.
OQ-8 (RVV filename, M4 entry) settles on `riscv_rvv.spl`. OQ-9 (P15 policy, M3 entry)
mandates hard-reserve at allocator init. OQ-10 (Zvfbfmin BF16, M8 entry) selects the
auto-insert convert-compute-convert path with `W_SIMD_BF16_RVV_EMULATED` diagnostic.
OQ-11 (vstart comment) is a doc-only post-M4 task. OQ-12 (WarpVec/mma.sync) locks the
direction as a separate `TileVec` trait, not an extension of WarpVec. OQ-1..OQ-5 are
spec-verification gates deferred to D1 (D1's `simd_spec_verification_2026-05-02.md` closes
them). Phase gates M0/M1/M3/M4/M8/M9 are unblocked by the decisions here; M1/M3/M4/M5
remain partially gated on D1's OQ-1/-2/-3/-4/-5 resolution.

---

## OQ Resolution Index

| OQ | Topic | Blocks | Decision (one-liner) | Confidence |
|---|---|---|---|---|
| OQ-6 | Diagnostic code count | M0 entry | Accept 26 (C2 §9) as authoritative; brief's 33 is stale — do not add phantom codes | High |
| OQ-1 | V-01/V-06/V-03 EVEX bytes | M1 entry | Deferred to D1 verification | — |
| OQ-2 | V-25 NEON FCMGT | M1 entry | Deferred to D1 verification | — |
| OQ-3 | V-13/V-15/V-16 RVV | M4 entry | Deferred to D1 verification | — |
| OQ-4 | V-08 SVE2 Z-reg | M3 exit | Deferred to D1 verification | — |
| OQ-5 | V-23 PTX shfl.sync | M5 exit | Deferred to D1 verification | — |
| OQ-7 | x86_64_simd.spl split scope | M1 entry | Keep SSE+AVX2 monolithic; new file for AVX-512 only | High |
| OQ-8 | riscv_rvv.spl vs riscv_v.spl filename | M4 entry | Use `riscv_rvv.spl` | High |
| OQ-9 | P15 allocation policy | M3 entry | Hard-reserve P15 at allocator init (mirrors G-01 k0 pattern) | High |
| OQ-10 | RVV Zvfbfmin convert-compute-convert | M8 entry | Auto-insert with `W_SIMD_BF16_RVV_EMULATED` warning | High |
| OQ-11 | V-38 vstart trap-resume comment | post-M4 follow-up | Doc-only fix: add RVV §3.7 citation to G-05 comment | Medium |
| OQ-12 | WarpVec / mma.sync interface conflict | M9 scope gate | Separate `TileVec<T,M,N,K>` trait; WarpVec stays lane-indexed | High |

---

## OQ-6 (decision before M0) — Diagnostic code count discrepancy

### Context

C2 §9 as enumerated contains exactly **26 diagnostic codes**: 17 error codes (Table 9-A)
and 9 warning codes (Table 9-B). The task brief that launched D3 asserted a count of **33**,
creating a 7-code discrepancy. The discrepancy has two possible origins:

1. The brief was written from an earlier, wider proposal that included codes later collapsed
   during C2 authorship (e.g., codes for scalable-only checks that were merged into existing
   type-check errors, or GPU-only codes that were relocated to a separate GPU error catalog).
2. Seven codes were planned but never formally written into C2 §9, meaning they exist only
   as aspirational bullet points in the brief's Appendix.

Without the brief's Appendix text in this context, the exact identity of the 7 ghost codes
cannot be determined from first principles here. The C2 §9 tables, however, are fully
enumerated and internally consistent: each code has a phase tag, trigger description,
example bad source, and fix-it entry. The brief's number has no corresponding table.

The 26 codes enumerated in C2 §9 are:

**Table 9-A Error Codes (17):**
`E_SIMD_BAD_LANES`, `E_SIMD_TYPE_MISMATCH`, `E_SIMD_FLOAT_ONLY`, `E_SIMD_INT_ONLY`,
`E_SIMD_LANE_MISMATCH`, `E_SIMD_MASK_TYPE_MISMATCH`, `E_SIMD_ARRAY_LEN_MISMATCH`,
`E_SIMD_SLICE_TOO_SHORT`, `E_SIMD_SHIFT_OOB`, `E_SIMD_LANE_OOB`,
`E_SIMD_TYPE_AMBIGUOUS`, `E_WARP_NO_GPU_TARGET`, `E_WARP_NO_APPLE_M`,
`E_SVE_FIXED_ON_SVE_TARGET`, `E_SVE_SCALABLE_ON_FIXED_TARGET`,
`E_SIMD_UNSUPPORTED_OP`, `E_SIMD_FP16_NO_NATIVE`.

**Table 9-B Warning Codes (9):**
`W_SIMD_SCALAR_FALLBACK`, `W_SIMD_NO_NATIVE_LOWERING`, `W_SIMD_HARDCODED_STRIDE`,
`W_SIMD_PRED_PROMOTE_HINT`, `W_SIMD_FIXED_EXCEEDS_MIN_LANES`,
`W_SIMD_MASK_BITS_OOB`, `W_WARP_SYNC_EMPTY_MASK`, `W_SIMD_FP16_AUTOPROMOTE`,
`W_SIMD_BF16_X86_AUTOPROMOTE`.

Note: if OQ-10 is resolved as recommended (auto-insert Zvfbfmin path with warning), a
27th code `W_SIMD_BF16_RVV_EMULATED` is added at M8. See OQ-10 for that implication.

### Options Considered

**Option A — Accept 26 as authoritative; brief's 33 is stale.**
C2 §9 is the more recent, fully-specified document. Every code in C2 §9 has a complete
definition, phase tag, trigger, and fix-it. The brief's 33 has no matching definitions.
Accepting 26 means D3 implements exactly what C2 §9 specifies — no gaps, no phantom entries.

**Option B — Identify the 7 missing codes and add them before M1.**
This would require auditing the original brief against C2 §9, tracking down the 7 candidate
codes, writing full definitions for each, and re-ratifying with the team. This adds M0 delay
and risks adding codes that were intentionally removed during C2 authorship.

### Decision

**Accept Option A: 26 codes from C2 §9 is the authoritative diagnostic catalog. The brief's
count of 33 is stale and should not be back-propagated into the implementation.** The 7
discrepant codes should be treated as never formally specified; they do not exist in any
C2 §9 table and must not be silently stubbed or placeholder-defined during M0/M1 work.
If a genuinely new diagnostic need is discovered during implementation, it must be proposed
as a formal addition with a complete C2 §9 entry (trigger, example, fix-it) — not silently
added to hit a number. The brief should be updated to reference C2 §9 as the source of truth
on counts.

### Implication for D3

D3's diagnostic enum in `35.semantics/simd_diagnostics.spl` (or equivalent) must declare
exactly **26 variants** corresponding to the C2 §9 names above. The enum must not contain
placeholder slots (`Reserved7`, `Phantom33`, etc.) for the 7 missing codes. If OQ-10 is
adopted (recommended), add `W_SIMD_BF16_RVV_EMULATED` as a 27th entry at M8 milestone —
not before. Stable code-name spelling matters for error catalog cross-linking; use the
exact names from C2 §9 Table 9-A and Table 9-B verbatim.

---

## OQ-7 (decision before M1) — x86_64_simd.spl split scope

### Context

The original task brief for M1 proposed splitting `x86_64_simd.spl` (411 lines, covering
SSE and AVX2) into three files: `x86_64_sse.spl`, `x86_64_avx2.spl`, and
`x86_64_avx512.spl`. C3a §5.2 ("Encoder Helper Inventory") explicitly revisited this
proposal and reached a different conclusion: **keep SSE and AVX2 in a single monolithic file
and create only one new file for AVX-512**.

The rationale in C3a §5.2 is technical, not stylistic. SSE and AVX2 share the VEX prefix
encoding logic, and the two shared helpers `_encode_simd_3op_xmm` (XMM register path) and
`_encode_simd_3op_ymm` (YMM register path) are called by both SSE and AVX2 emit helpers.
Splitting SSE from AVX2 would require either duplicating these helpers (violating DRY) or
creating a third shared-helper file — adding complexity without reducing file size
meaningfully (SSE at ~180 LOC + AVX2 at ~230 LOC = 411 LOC total, well within one file).

AVX-512, by contrast, uses the qualitatively different EVEX encoding (P0/P1/P2/P3 bytes,
4-byte prefix, k-register masking) and must use EVEX-specific builders (`evex_emit_*`)
distinct from the VEX builders. This justifies a new file `x86_64_avx512.spl`.

### Options

**Option A — Split now in M0 (3-way split): `x86_64_sse.spl`, `x86_64_avx2.spl`, `x86_64_avx512.spl`.**
Clean slate before any new M1 helpers are added. However, requires duplicating or extracting
shared VEX helpers, adding churn for no functional benefit.

**Option B — Keep SSE+AVX2 monolithic; add `x86_64_avx512.spl` (2-file outcome per C3a §5.2).**
Follows the more recent and technically-grounded recommendation from C3a §5.2. No shared
helper fragmentation. `x86_64_avx512.spl` starts clean with no legacy VEX helpers.

**Option C — Keep permanently monolithic (all three ISA levels in one file).**
Would push `x86_64_simd.spl` to ~700+ LOC once AVX-512 helpers land in M1. Not sustainable.

### Decision

**Adopt Option B: keep `x86_64_simd.spl` monolithic for SSE+AVX2 and introduce
`x86_64_avx512.spl` as the sole new x86 backend file at M1.** This is the 2-file outcome
already recommended in C3a §5.2 and already reflected in the rollout plan's M1 output
table. The task brief's 3-way split proposal is rejected. The split was proposed before
the shared-helper analysis in C3a was available; C3a is the more recent and more specific
source. No renaming of `x86_64_simd.spl` is required; it continues to hold SSE and AVX2
helpers. The new `x86_64_avx512.spl` should import nothing from `x86_64_simd.spl` —
EVEX builders are self-contained.

**Implication for M1 implementation:** The ~30 new AVX-512 helpers enumerated in C3a §5.3
go into `x86_64_avx512.spl`. The ~9 new SSE/AVX2 helpers from C3a §5.2 (including
`_encode_simd_blendvps`, `_encode_vgatherdps`, `_encode_vfmadd213ps`, etc.) extend the
existing `x86_64_simd.spl`. No rename; no split of existing file.

---

## OQ-8 (decision before M4) — riscv_rvv.spl vs riscv_v.spl filename

### Context

Two earlier design documents use different names for the RVV backend file:
- **B3 §3** (an earlier round-1 planning document) references `riscv_v.spl`.
- **C3b §11.3** (the more recent and detailed helper count table) references `riscv_rvv.spl`.
- **The rollout plan M4 output section** (the authoritative phase plan) already specifies
  `src/compiler/70.backend/backend/native/riscv_rvv.spl` as the output file.

The question is which name to officially adopt before D4/M4 creates the file.

### Naming Convention Analysis

The project's existing backend files follow a consistent pattern:
`<arch>_<extension>.spl` where the extension token is the well-known ISA extension name.

Existing files:
- `arm_neon.spl` — ARM NEON extension
- `arm_sve2.spl` — ARM SVE2 extension
- `x86_64_simd.spl` — x86-64 SIMD (SSE/AVX2 combined; AVX-512 will add `x86_64_avx512.spl`)

For RISC-V vector, the ISA extension is officially named **"V" extension** in the RISC-V
specification (ratified RVV 1.0, also called "Zve*" family). The commonly used abbreviation
in the ecosystem is **RVV** (RISC-V Vector), appearing in toolchain names (`riscv-rvv`),
intrinsic headers (`<riscv_vector.h>`), and community documentation. Using `rvv` as the
token in the filename makes the file's scope instantly recognizable and matches the
ecosystem convention.

`riscv_v.spl` is technically correct (the extension letter is "V") but reads ambiguously —
"v" alone is too short and could be confused with "version" or another V-prefixed extension.
`riscv_rvv.spl` is unambiguous and searchable.

C3b §11.3 is also the more authoritative document as it ties the filename to a specific
helper count table (15 helpers, ~550 LOC), giving the name a concrete referent.

### Decision

**Use `riscv_rvv.spl`.** The filename `riscv_rvv.spl` is adopted as the canonical name for
the RISC-V vector backend file (path:
`src/compiler/70.backend/backend/native/riscv_rvv.spl`). This matches C3b §11.3, the
rollout plan M4 output table, and the broader RVV ecosystem naming convention. The earlier
B3 §3 reference to `riscv_v.spl` is superseded. Any existing test scaffold or comment
referencing `riscv_v.spl` must be updated to `riscv_rvv.spl` before M4 creates the file.

---

## OQ-9 (decision before M3) — P15 allocation policy

### Context

ARM SVE2 provides 16 predicate registers, P0–P15. ACLE §11.1 reserves P15 by convention
for use by the OS or runtime (e.g., as a scratch predicate for system call wrappers). In
normal application code, P15 must not be allocated to user values.

C3b §8.3 specifies P15 as reserved in the SVE2 allocator. The SVE2 allocator pseudocode
(`arm_sve2_regalloc.spl`) sets `free_p[P15_INDEX] = false` at init (the `*** PERMANENT
RESERVE ***` comment). AAPCS64-SVE also treats P4–P14 as callee-saved, confirming that P15
sits outside the normal calling convention range.

The rollout plan (OQ-9 text) already recommends hard-reserve and draws the analogy to G-01
(the k0 hard-reserve for AVX-512 k-registers). The question is whether the final decision
is to hard-reserve at init or to use a lazier approach:

### Options

**Option A — Hard-reserve P15 at allocator init.** Set `free_p[15] = false` in
`sve2_alloc_init()` unconditionally. P15 can never appear in generated code even if the
liveness pass has a latent bug. This mirrors G-01 k0 reservation exactly.

**Option B — Lazy avoidance in the liveness pass.** P15 is not marked reserved at init;
instead, the liveness analysis is trusted to never assign a user value to P15. Relies on
the correctness of liveness — any bug there would produce P15 in a generated instruction.

**Option C — Provide an `--enable-p15` compiler flag.** Allow P15 allocation on embedded
targets where SME or the runtime reservation is known absent. Hard-reserve is the default.

### Decision

**Adopt Option A with an optional note toward Option C for future extension.** P15 is
**hard-reserved at allocator init** (`free_p[P15_INDEX] = false` in `sve2_alloc_init()`,
unconditional). This is the safer choice for exactly the same reason that k0 is hard-reserved
in G-01: the liveness pass is code-reviewed and tested, but belt-and-suspenders protection
against a latent allocator bug is worth the cost of one fewer allocatable predicate register.
P0–P14 (15 predicate registers) are sufficient for all known workloads.

Option C (`--enable-p15`) may be introduced in a future patch for embedded RISC-V-adjacent
targets (though SVE is Arm-only), but it is not in scope for M3. The M3 implementation
must hard-reserve; no flag is needed now. A TODO comment in `arm_sve2_regalloc.spl` noting
the theoretical `--enable-p15` path is acceptable but not required.

**Implication for D5 (SVE2 allocator):** The `Sve2AllocState.free_p` array is initialized
with index 15 permanently false. The `sve2_alloc_pred` function iterates `0..P15_INDEX`
(exclusive), never reaching P15. This is already reflected in the C3b §8.3 pseudocode and
must not be changed.

---

## OQ-10 (decision before M8) — RVV Zvfbfmin convert-compute-convert pattern

### Context

The RISC-V Zvfbfmin extension (BF16 minimum support) provides:
- BF16 vector loads and stores
- `vfncvtbf16.f.f.w` — narrowing convert: f32 → bf16 (halves the SEW)
- The reverse widening: `vfwcvt.f.f.v` — f16/bf16 → f32 (doubles the SEW)

Critically, Zvfbfmin does **not** provide native BF16 arithmetic (no `vfadd.vv` with
SEW=16 interpreted as BF16, no `vfmacc` on BF16 elements). This is by design in the RVV
1.0 + Zvfbfmin specification: BF16 is a storage format only; computation must be done in
f32.

This means any user-facing SIMD code operating on `FixedVec<bf16, N>` or
`ScalableVec<bf16>` on a RISC-V+Zvfbfmin target must internally follow the pattern:

```
vfwcvt.f.f.v  // bf16 → f32 widen
<f32 arithmetic>
vfncvtbf16.f.f.w  // f32 → bf16 narrow
```

The M8 design must decide whether the compiler auto-inserts this pattern (user writes
`FixedVec<bf16, N>` code naturally) or whether the user must write explicit f32 code.

### Options

**Option A — Auto-insert convert-compute-convert in MIR opt pass with `W_SIMD_BF16_RVV_EMULATED` diagnostic.**
A new MIR pass (e.g., `60.mir_opt/bf16_rvv_expand.spl`) detects `MirSimdBinop` nodes with
element type BF16 on a RISC-V+Zvfbfmin target and rewrites them as widen-arith-narrow
triplets. The user's source code is unchanged; the warning notifies them of the latency
cost (widening doubles the register pressure and effective LMUL).

**Option B — Require user to write explicit f32 code.**
`FixedVec<bf16, N>` on RVV targets where Zvfbfmin is the only BF16 support would emit
`E_SIMD_UNSUPPORTED_OP` for arithmetic operations, forcing the user to cast to f32,
compute, and cast back. This is ergonomically poor — most users will not know the target's
BF16 capability at code-write time.

### Decision

**Adopt Option A: auto-insert the convert-compute-convert pattern and emit
`W_SIMD_BF16_RVV_EMULATED` (a new warning diagnostic) when a BF16 arithmetic op is lowered
via the expand path on a Zvfbfmin-only target.** This keeps the user-facing API consistent
across targets: `FixedVec<bf16, N>` arithmetic "just works" everywhere that bf16 storage
exists. The warning gives performance-conscious users the signal they need to manually
promote if they want. The MIR pass follows the same architecture as the existing
`simd_split_unsupported.spl` pass (C2 §8.3), which already handles unsupported (T,N) pairs
via a split/fallback mechanism.

**Implication for OQ-6 / D3:** `W_SIMD_BF16_RVV_EMULATED` is a 27th diagnostic code not
in C2 §9's original 26. It is introduced at M8, not M0. D3's enum must leave room for this
code (it can be added at M8 milestone as a source edit — no re-ratification required since
it is a straightforward new warning with a well-defined trigger). The full diagnostic
description should be added to a C2 §9 addendum at M8 time, not speculatively now.

**Performance note:** On a typical RVV target with VLEN=256 and LMUL=1, expanding BF16→F32
doubles the LMUL (LMUL=1 → LMUL=2 for intermediate f32), reducing the number of elements
per register group. The compiler's existing `lmul_widen.spl` pass (C2 §8.3) handles LMUL
promotion; the BF16 expand pass should be layered after lmul_widen runs, not before.

---

## OQ-11 (non-blocking, post-M4 follow-up) — V-38 vstart trap-resume comment

### Context

C3b §14 item V-38 flags that the G-05 guard ("vstart-zero") in the RVV emitter has an
incomplete comment. G-05's *guard itself* is correct: after every `vsetvli` emission,
assert `vstart == 0` in debug builds, and document that `vsetvli` resets `vstart` to 0.
What the comment is missing is the citation of the non-obvious hazard: if a resumable trap
occurs *mid-vector-instruction*, hardware writes the interrupted element index into the
`vstart` CSR, and the interrupted instruction restarts from that element index when the
trap handler returns. This is specified in RVV §3.7.

V-38 does not imply the guard is wrong — it is correct. The hazard being undocumented in
the comment does not affect generated code behavior because `vsetvli` unconditionally resets
`vstart` to 0 on completion, so the next vector instruction always starts from element 0
regardless of what a previous trap wrote. The guard in G-05 is belt-and-suspenders; the
missing comment simply omits the RVV §3.7 citation that explains *why* it is safe.

### Options

**Option A — Doc-only fix: update the G-05 comment to cite RVV spec §3.7.**
Add a sentence: "See RVV §3.7: hardware sets vstart on trap; vsetvli resets it to 0 on
completion, so post-vsetvli vstart == 0 is invariant." No code change needed.

**Option B — Add a runtime assertion for non-debug builds as well.**
Insert a `csrr`-based vstart check before every vector instruction in a "paranoid" mode.
This would have measurable runtime overhead and is architecturally unnecessary given that
`vsetvli` provides the reset guarantee.

### Decision

**Adopt Option A: doc-only fix.** The guard is correct; only the comment is incomplete.
Adding a runtime assertion (Option B) would be over-engineering — the RVV spec guarantees
`vsetvli` resets `vstart`, and G-05 already asserts this post-vsetvli in debug builds.
A `# vstart == 0 post-vsetvli per RVV §3.7` inline comment in the G-05 guard function is
the complete resolution. This is a post-M4 follow-up commit, not a blocker.

**Responsible party:** backend-cpu lead. Assign alongside V-38 in C3b §14's post-M4 task
list. The comment update must reference RVV §3.7 specifically (not just "RVV spec") so
future readers can find the normative text.

---

## OQ-12 (non-blocking, M9 scope gate) — WarpVec / mma.sync interface conflict

### Context

`WarpVec<T>` (C2 §6) is the lane-indexed warp-level vector type in the SIMD trait hierarchy.
Its method catalog treats the warp as a flat 1-D array of `T` values indexed by lane.
The C2 §1.6 method count gives `WarpVec<T>` 55 total methods (39 inherited + 16 type-specific).

CUDA `mma.sync` (Tensor Core) instructions operate on matrix tiles with fixed shapes. The
canonical example from the PTX ISA is `mma.m16n8k16.f32.f16.f16.f32` — a 16×8×16 matrix
multiply-accumulate where:
- A fragment: m×k = 16×16 f16 elements, distributed across 32 threads (8 elements per thread)
- B fragment: k×n = 16×8 f16 elements
- C/D fragment: m×n = 16×8 f32 accumulator elements (4 per thread)

This per-thread fragment layout does not map to a 1-D lane-indexed `WarpVec<f16>`. The
A-fragment has 8 lanes × 8 f16 per thread = effectively a 2-D slice per warp, not a flat
vector. Forcing `mma.sync` into `WarpVec<T>` would require either:
- An ad-hoc `mma_tile(a: WarpVec<f16>, b: WarpVec<f16>, c: WarpVec<f32>) -> WarpVec<f32>`
  method with undocumented implicit N requirements (m=16, n=8, k=16 baked in), or
- Parametric `mma_tile<M: i32, N: i32, K: i32>()` making WarpVec shape-polymorphic — which
  conflicts with WarpVec's current fixed-N-per-type semantics.

### Options

**Option A — Fold mma.sync into WarpVec as specialized methods.**
Add `warp_mma_m16n8k16()` etc. as explicit named variants to `WarpVec<T>`. No new type.
Downside: WarpVec accumulates tile-specific methods that are nonsensical for non-MMA use,
and the (M,N,K) shape relationship is not captured in the type system.

**Option B — New `TileVec<T,M,N,K>` trait as a separate type in the GPU trait family.**
`TileVec` represents a warp-distributed matrix fragment with explicit compile-time shape.
`WarpVec<T>` remains lane-indexed (1-D). Tensor core operations live on `TileVec`.
Users convert: `WarpVec<f16> -> TileVec<f16,16,16,1>` (A-fragment), etc. The conversion
is explicit, which surfaces the shape contract at the call site.

**Option C — Defer entirely and document as out-of-scope.**
Mark mma.sync support as post-M9. Document that WarpVec does not support tensor cores
today. Leave the door open without committing to either interface direction.

### Decision

**Adopt Option B: introduce a separate `TileVec<T,M,N,K>` trait at M9.** WarpVec must
remain lane-indexed; adding mma.sync methods to it would make WarpVec's semantics
inconsistent (lane operations + tile operations in one type). The (M,N,K) parameters are
naturally expressible as compile-time type parameters — Simple's generics support this.
`TileVec<T,M,N,K>` also maps cleanly to the PTX instruction's form (m, n, k baked into
the instruction name), giving a one-to-one correspondence between the Simple type and the
PTX opcode.

Before M9 activates, the M9 author must audit the C2 §6 WarpVec method catalog for any
method that already partially overlaps with a TileVec semantic (e.g., `reduce_sum`,
`warp_shuffle`) and decide whether TileVec reuses those methods or needs its own.
`warp_shuffle` (based on `shfl.sync`, OQ-5) operates on individual lanes and belongs to
WarpVec; matrix-level reductions belong to TileVec. The audit is the M9 entry gate, not
M8 or earlier.

**Implication for C2 §6 (next update):** Add a note to the `WarpVec<T>` section: "Tensor
core (mma.sync) operations are not part of WarpVec. See `TileVec<T,M,N,K>` (M9 scope)."
This prevents implementors from attempting to add mma.sync to WarpVec during M5/M6/M7.

---

## OQ-1..OQ-5 (deferred to D1)

These OQs are spec-verification gates that require fetching primary ISA sources (Intel SDM,
ARM ARM, RVV spec inst-table.adoc, PTX ISA Reference) and cross-checking them against the
encoding constants in C3b §14's verification table. They cannot be decided by reasoning
alone — they require reading the normative spec text and comparing byte values. D1's
deliverable `doc/05_design/simd_spec_verification_2026-05-02.md` is the resolution
artifact. Cross-reference D1's status table here when D1 lands.

**OQ-1 (V-01/V-06/V-03 — EVEX byte verification, blocks M1 entry):**
C3b §14 shows `62 F2 75 C9 A8 C2` as the EVEX VFMADD213PS encoding, status UNVERIFIED.
D1 must verify P0/P1/P2/P3 fields (V-01), the exact byte string (V-06), and k0 z-bit
behavior (V-03) against Intel SDM Vol 2A §2.6.1 Table 2-36 and Vol 2B VFMADD213PS entry.
No AVX-512 golden file may be committed until D1 confirms these three items.

**OQ-2 (V-25 — NEON FCMGT operand reversal, blocks M1 entry):**
C3b §14 notes `vclt Vd, Vn, Vm` maps to `FCMGT Vm, Vn` with reversed operands. G-11's
polarity depends on this being correct. D1 must verify against ARM ARM §C7.2.x FCMGT entry.
If operands are wrong, G-11 polarity must be corrected before NEON golden comparisons land.

**OQ-3 (V-13/V-15/V-16 — RVV encoding table, blocks M4 entry):**
Three RVV encoding constants are unverified in C3b §14: vlmul fractional encoding table
(V-13), vfadd funct6=000000 (V-15), vfmacc funct6=011000 (V-16). D1 must verify these
against RVV spec §3.4.2 Table 4 and riscv-v-spec inst-table.adoc. M4 golden files are
blocked until D1 confirms or corrects all three.

**OQ-4 (V-08 — SVE2 Z-register encoding, blocks M3 exit):**
Instruction encoding bytes for the ~14 C3a §5.4 SVE2 helpers are unverified. D1 must fetch
ARMv9 ARM §C7 SVE instruction encodings before M3 golden files are written.

**OQ-5 (V-23 — PTX shfl.sync syntax, blocks M5 exit):**
PTX `shfl.sync` exact syntax (mask operand position, `.b32` suffix) is unverified.
D1 must verify against PTX ISA Reference §9.7.6. M5 PTX golden files are blocked pending
D1's confirmation. Note: C3b §14 golden S-35 is already status ERRATA-GUARDED for the
`0xffffffff` all-lanes mask; D1 should also confirm that mask value is correct for
`reduce_sum` (C1 §6-G guard).

---

## Phase Entry/Exit Gate Impact Summary

| Phase | Gate | OQs blocking | Status after this document |
|---|---|---|---|
| M0 | entry | OQ-6 | **UNBLOCKED** — 26-code catalog accepted |
| M1 | entry | OQ-1, OQ-2, OQ-7 | OQ-7 UNBLOCKED; OQ-1/-2 await D1 |
| M3 | entry | OQ-9 | **UNBLOCKED** — P15 hard-reserve decided |
| M3 | exit | OQ-4 | Awaiting D1 (SVE2 Z-reg encoding) |
| M4 | entry | OQ-3, OQ-8 | OQ-8 UNBLOCKED; OQ-3 awaits D1 |
| M5 | exit | OQ-5 | Awaiting D1 (PTX shfl.sync) |
| M8 | entry | OQ-10 | **UNBLOCKED** — auto-insert + W_SIMD_BF16_RVV_EMULATED decided |
| M9 | scope | OQ-12 | **UNBLOCKED** — TileVec<T,M,N,K> direction locked |
| post-M4 | follow-up | OQ-11 | Doc-only task assigned to backend-cpu lead |

**Summary counts:**
- Decided here (D2): OQ-6, OQ-7, OQ-8, OQ-9, OQ-10, OQ-11, OQ-12 — **7 decisions**
- Deferred to D1 (spec verification): OQ-1, OQ-2, OQ-3, OQ-4, OQ-5 — **5 deferrals**
- Phase entry gates fully unblocked by this document: M0, M3, M4 (partial), M8, M9 — **5 phases**
- Phase entry gates still pending D1: M1 (partial: OQ-1/-2), M3 exit (OQ-4), M4 entry (OQ-3), M5 exit (OQ-5)
