# Cert Phase-4 stress/robustness findings

Confirmed defects discovered while building `scripts/check/cert/stress-suite.shs`,
reproduced on the deployed clean compiler
`bin/release/x86_64-unknown-linux-gnu/simple` (default compiled backend unless
noted). Each is re-run live (non-gating) by the suite's FINDINGS section so the
defect is demonstrated, not merely asserted. They mark the honest boundary of
the CORE regression envelope, which stays within the safe region below.

## f01 — deep-nesting stack overflow (CRASH, not a clean diagnostic)
`f01_deep_nest_stackoverflow.spl` — a single expression with 5000 balanced
parentheses. The recursive-descent parser overflows its native stack and the
process **aborts** (`thread 'simple-main' has overflowed its stack; fatal
runtime error: stack overflow` → SIGABRT, exit 134) instead of emitting a
bounded "nesting too deep" diagnostic. The same overflow occurs for an
*unterminated* deep nest (see suite `mal_unterminated_nest` at safe depth 500,
which rejects cleanly; ~4500–5000 open parens overflows).
- Observed threshold: depth 1000/2000/3000/4000 parse fine; ~5000+ aborts.
- Impact: an untrusted or generated source file can crash the compiler.
- Expected robust behavior: reject over-deep nesting with a bounded error.

## f02 — large integer literal codegen is wrong (SILENT-WRONG)
`f02_bigint_literal_codegen.spl` — `print(9223372036854775807)` (i64 max).
- compiled backend prints `-1`; interpreter prints `9223372036854775807`.
- `print(4611686018427387904)` (2^62): compiled prints `0`, interpreter correct.
- Literals below ~2^62 (e.g. `1000000000000`) are correct in both modes.
- Impact: silently wrong results for large integer constants in compiled code.
  The CORE suite pins large-literal cases only in the safe range.

## f03 — many function calls in one expression give wrong sum (WRONG / DIVERGENCE)
`f03_manycall_sum_wrong.spl` — sum of 300 calls `f0()+...+f299()` where
`fi()` returns `i`; the correct sum is `44850`.
- compiled backend prints `64695813934153728`; interpreter prints `44786`.
- Both differ from 44850, so this is a genuine defect (not just a codegen diff);
  summing 300 integer *literals* is correct in both modes, so the fault is in
  evaluating a long chain of function-call operands.
- Impact: incorrect results for wide call-chain expressions. The CORE suite's
  many-functions case therefore defines 300 functions but calls only a few.
