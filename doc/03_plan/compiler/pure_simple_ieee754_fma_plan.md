# Pure-Simple IEEE-754 FMA Implementation Plan

## Scope and current gap

This plan extends the selected full SIMD bootstrap requirements and design; it
does not replace them. `src/lib/common/math/ieee754_bits.spl` already owns bit
classification, binary32 widening, binary64-to-binary32 round-to-nearest-even,
and public `math_f32_fma_bits`/`math_f64_fma_bits`. The binary32 path uses an
exact binary64 product plus TwoSum residual, but the binary64 path calls
`std.common.math.math.math_fma`, whose final implementation crosses a native
C/Rust primitive boundary. The interpreter and SIMD lane code consequently do
not yet provide a pure-Simple scalar oracle for binary64.

## Required semantics

- **FMA-001:** Compute `a*b+c` with one final IEEE-754 binary32 or binary64
  round, round-to-nearest ties-to-even. Intermediate product/addition must not
  round to the destination format.
- **FMA-002:** Preserve deterministic first-NaN payload selection and quiet a
  signaling NaN. Define and test the sign/payload result for every NaN position.
- **FMA-003:** Return invalid-operation quiet NaN for `infinity*zero` and for an
  infinite product cancelled by opposite-signed infinity.
- **FMA-004:** Preserve signed-zero rules for exact zero, including product-zero
  plus addend-zero and exact finite cancellation. Gradual underflow is required;
  subnormal inputs and outputs may not flush to zero.
- **FMA-005:** Correctly round carry into the next binade, finite overflow to
  signed infinity, and normal/subnormal boundaries.
- **FMA-006:** Interpreter scalar, fixed SIMD lanes (`Vec16f`, `Vec8d`, and
  existing widths), AVX-512 native execution, and scalar fallback share one
  bit-exact oracle. The final semantic path has no C/Rust FMA dependency.

## Algorithm decision

Implement exact integer-significand accumulation in pure Simple. Decode each
operand into sign, class, unbiased exponent, and an integer significand (24 bits
for binary32, 53 for binary64). Resolve special classes first. For finite
values, multiply significands exactly, align the product and addend in a signed
wide accumulator with at least the full product width plus guard, round, and
sticky information, then add/subtract by sign, normalize, and perform one
ties-to-even pack into the destination format.

Binary32 can use an `i64` exact accumulator. Binary64 needs 106 product bits and
exponent-distance sticky handling; use a small pure-Simple unsigned multiword
integer (`lo`, `hi`, plus sticky) rather than floating intermediates. Required
operations are 53x53 multiply using 32-bit limbs, magnitude compare, signed
add/subtract, bounded shifts that accumulate discarded-bit sticky state,
leading-bit normalization, and final guard/round/sticky packing.

Rejected alternatives:

| Alternative | Benefit | Cost/reason rejected |
| --- | --- | --- |
| Dekker/TwoProduct with ordinary f64 | Small implementation | Depends on exact evaluation/rounding properties and is fragile at overflow, underflow, and cancellation boundaries. |
| Arbitrary-precision general integer | Easy proof reuse | Excess allocation and complexity on every scalar/lane operation. |
| Native `fma` oracle | Hardware speed | Violates pure-Simple bootstrap and makes interpreter behavior host-dependent. |

## File and phase ownership

1. **Research/proof:** append algorithm invariants and IEEE special-case table
   to this plan and `doc/05_design/full_pure_simple_simd_bootstrap.md`.
2. **Exact arithmetic owner:** add private multiword helpers beside
   `ieee754_bits.spl`, or split them to
   `src/lib/common/math/ieee754_fma_integer.spl` if the owner exceeds the source
   size limit. Public API remains the two `*_fma_bits` functions.
3. **Scalar integration:** replace `math_f64_fma_bits`' native call and remove
   `math_fma` imports from the IEEE owner. Keep native math APIs only for other
   callers until a separate migration proves they are unused.
4. **Interpreter/SIMD integration:** retain
   `src/compiler/95.interp/mir_simd_interpreter.spl` and
   `src/lib/common/simd_fallback.spl` as consumers of the shared bit oracle;
   remove any direct extern dispatch from their FMA path.
5. **Native AVX-512 owner:** compare emitted `VFMADD213PS/PD` lane results with
   the scalar oracle. Capability denial and tail lanes use the same pure-Simple
   fallback. No software helper may silently advertise AVX-512 execution.
6. **Boundary cleanup:** after call-graph proof, remove FMA-only registrations
   from Rust `interpreter_extern/math.rs` and `mod.rs` and any C runtime symbol.
   This is the final phase so bootstrap remains runnable during migration.
7. **Review:** highest-capability review of arithmetic proof, special cases,
   test vectors, branch coverage, and native-boundary absence before admission.

## Verification matrix

Unit tests assert exact output bits for: all sign combinations; `+0/-0` product
and addend; exact cancellation; smallest/largest subnormal; normal/subnormal
ties; halfway-even and halfway-odd; significand carry; maximum finite overflow;
each infinity case; quiet/signaling NaNs in each operand with payloads; and
large-cancellation examples where separate multiply/add or double rounding
differs from FMA. Include deterministic generated triples around every exponent
boundary and compare a checked-in, independently generated bit-vector corpus.

Integration tests execute identical triples through scalar bit helpers,
interpreter scalar expressions, SIMD fallback lanes, `Vec16f`, `Vec8d`, and an
admitted AVX-512 native fixture. Compare bit arrays, including tail lengths
`0, 1, lanes-1, lanes, lanes+1`. A source/closure test rejects `math_fma`,
`rt_math_fma`, or equivalent foreign dependencies reachable from the oracle.
Mutation checks must fail when sticky propagation, tie-even parity, zero sign,
NaN quieting, or invalid-operation handling is removed.

Target branch coverage is at least 90% for the exact arithmetic owner and 100%
for special-class branches. Every uncovered branch needs a written unreachable
proof or an added vector.

## Performance and NFR gates

The baseline is the current scalar native primitive and current SIMD fallback,
measured outside correctness tests using the same admitted binary and corpus.
Optimize only after bit parity: inline fixed-size limb operations, avoid arrays
and heap allocation, fast-path ordinary finite operands with bounded exponent
distance, and keep a cold special-case path. The fast path must fall back to the
exact multiword path before losing any guard/sticky information.

Record p50/p95 latency and operations/second for scalar f32/f64 plus lane
throughput for fallback and AVX-512. Initial admission target: no allocation in
the hot finite path; scalar pure-Simple throughput at least 25% of the native
primitive baseline; fallback vector throughput no worse than 15% below repeated
scalar pure-Simple; AVX-512 at least 4x scalar on qualified hardware. A missed
performance target is reported as a concrete blocker and never relaxed through
non-fused arithmetic or host-native dependency.

## Completion gates

Completion requires exact corpus parity, edge/mutation coverage, branch target,
interpreter and vector parity, qualified AVX-512 native evidence, source closure
showing no native FMA dependency, and updated requirements/design/test manuals.
Hardware-unavailable AVX-512 rows remain BLOCKED with their exact resume command;
they cannot be represented by interpreter success.
