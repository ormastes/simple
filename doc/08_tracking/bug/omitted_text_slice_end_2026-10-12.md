# Omitted text-slice endpoint reaches native code as explicit minus one

- Bug ID: `omitted_text_slice_end_2026-10-12`.
- Status: pure Simple bridge repair passes confined actual-source regression;
  embedding in a successor pure Simple producer and native verification pending.
- Authoritative bug-database reconciliation pending: no qualified database CLI
  was used. This report supersedes the provisional adapter-specific ID
  `phase2_adapter_omitted_text_slice_endpoint_2026_10_12`.
- Owner: compiler frontend flat AST bridge. No runtime workaround is applied.
- Applied source repair: local commit `bb2cf6f34f3`; this identifies the bridge
  and regression-spec changes, not a rebuilt or admitted compiler artifact.

## Observed native failure

The retained Phase2 diagnostic adapter was linked strictly from 42 genuine f2
objects, the qualified entry object and pinned core-C runtime. Its SHA-256 is
`16ea523274017e990e1ee68091bafbd14082565e6e38f51b29dc321476f161d5`.
Its no-argument usage control passed; fully populated sentinel and bad-inventory
controls returned usage instead of reaching their intended guards.

`build/native_probe/phase2-adapter-f2-20261012-sol/manual-link3/parse_args_actual.disassembly.txt`
contains five `spl_str_slice` calls for the five `arg[n:]` flag suffixes.
The source-root call passes start 14 and end -1. The linked
`runtime_legacy_core.c` clamps an end smaller than start to start, yielding an
empty suffix. This proves a bad emitted endpoint. No dynamic branch trace proved
that this alone caused the adapter's observed usage responses; another argv
defect is not excluded. The adapter's three-cycle cap remains closed.

## Root cause and repair

Both postfix parsers in `core/parser_expr.spl` encode an omitted endpoint as a
synthetic `EXPR_INT_LIT(-1)`. User-written `-1` is `EXPR_UNARY` over integer 1;
parentheses preserve that expression, and `1 - 2` is a binary expression.
`_FlatAstBridge/convert_nodes.spl` previously forwarded every endpoint as the
second argument of `slice`, erasing omission before MIR lowering.

The repair consumes the parser's existing marker: the synthetic literal creates
a one-argument method call, while every explicit endpoint keeps two arguments.
Receiver, start, span and explicit-end expressions retain their existing shapes.
Both existing MIR text-slice paths already evaluate a call receiver once and use
that value for `spl_str_len` and `spl_str_slice`; no second receiver expression
is synthesized. The repair adds no source scans, persistent cache or runtime
allocation beyond the existing slice implementation.

This is a parser/bridge representation contract, not provenance encoded in the
integer value. A direct flat-AST API client constructing `IntLit(-1)` as the end
still uses the reserved omission marker. A future constant-folding pass before
the bridge must preserve omission separately rather than fold explicit negative
expressions into that marker.

## Runtime and Rust seed comparison

The linked core-C `spl_str_len` uses `strlen` and `spl_str_slice` copies byte
ranges. Full `runtime.c` uses byte lengths too, but resolves negative endpoints
relative to length, so its explicit -1 excludes the last byte. Changing runtime
libraries or globally treating -1 as omission would change explicit bounds.
This repair leaves both runtimes' current explicit-negative policy untouched.

Rust seed parser `expressions/postfix.rs` preserves optional endpoints. Its HIR
`lower/expr/collections.rs::lower_slice` lowers an omitted end to `i64::MAX`,
clamped by `rt_slice`; explicit negative ends are lowered as expressions. The
Rust string slice runtime uses byte lengths and raw byte ranges. The seed does
not share this bridge bug and requires no matching source change. No conversion
to codepoint indices or new UTF-8 boundary policy is introduced.

## Reproducible evidence and limits

Packet: `build/native_probe/omitted-text-slice-end-20261012-sol/`.
Regression: `test/01_unit/compiler/frontend/omitted_text_slice_end_spec.spl`.
The immutable d958 Rust seed is used only as an explicitly authorized source
diagnostic, not as a replacement product compiler. A private snapshot contains
19,244 files from actual compiler/lib/app/compositions sources. The direct real
test runner executes the real parser and bridge; no parser or bridge substitutes
are used. The baseline/candidate manifests differ in exactly the bridge owner.

| Run | Executed | Passed | Failed | Peak KiB | Exit | Final job count |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Baseline | 11 | 4 | 7 | 438396 | 1 | 0 |
| Candidate | 11 | 11 | 0 | 437188 | 0 | 0 |

Each run records 1,614 traced reads, zero outside-source reads and unchanged
source pins. Cases cover start zero/nonzero/end/beyond-end, empty receiver, UTF-8
byte-boundary start, explicit negative/parenthesized/arithmetic endpoints,
positive/zero bounds and retention of a call receiver exactly once in the AST.
Measured durations were 6320 ms baseline and 6396 ms candidate; these single
diagnostic samples are not a performance benchmark.

Earlier preserved launcher failures executed zero cases: missing output parent,
missing LLVM DLL, and the nested `test` wrapper's early child death. The corrected
direct-runner baseline/candidate batch is terminal; do not replay its green spec.
Receipts disable RSS termination, retain wall/log/disk caps and close job trees.

Native execution of the repaired producer, dynamic receiver-effect counting,
and UTF-8 output verification remain unrun. The next qualification step must use
a successor producer embedding this repair; the existing adapter is not rebuilt.
No Phase1/Phase2/Phase3 release claim follows from these source assertions.
The six full LLVM/Cranelift compiler/interpreter/loader products remain 0/6
qualified with zero original product cases executed in this lane.
