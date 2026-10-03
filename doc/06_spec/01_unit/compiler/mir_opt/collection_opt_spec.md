# MIR collection optimization specification inventory

Status: **authored replacement for stale generated output; unexecuted**
(2026-10-03). Source:
`test/01_unit/compiler/mir_opt/collection_opt_spec.spl`.
This is not a generated manual or runtime PASS. Its 51 scenarios call actual
MIR pass/canonicalizer APIs and inspect rewritten instructions and counters;
they do not execute the rewritten program or prove driver pipeline admission.

Run with an admitted pure-Simple self-hosted test runner that executes `it`
bodies. No Rust-seed fallback is permitted. No runtime command was run for
this increment; the test-first commit precedes implementation without claiming
an observed assertion RED.

## Authority and key contract

Runtime-looking text alone is not a resolved runtime identity. Fresh passes
admit no query callees. Positive fixtures use `_co_admitted_pass`, explicitly
calling `admit_collection_runtime_reads` with known runtime read names. The
setter replaces the set and rejects unknown names. Production callers still
need external proof that admitted names denote the trusted runtime functions;
this fixture admission is not that compiler proof.

Legacy `is_pure_method` classification remains compatible but is not CSE
purity authority. Original bare `has`, `contains`, subset and disjoint cases
are retained with changed expectations: both calls remain and reuse is zero.
Bare/unknown calls also invalidate previously cached runtime reads.

Query keys must distinguish type, payload, argument boundaries and arity.
Exact supported scalar repeats and stable locals may reuse. Equal string
literal bytes do not prove equal allocation/pointer identity, so strings and
aggregates fail closed without a per-operation identity proof. Floating-point text is not a bitwise identity
proof. Move operands are consuming and cannot become cached copies. A local
redefinition or consumed/overwritten result invalidates the relevant cached
answer, including definitions produced by another admitted query.

## New regression inventory

| REQ-MIR-COLLOPT suffix | Concrete observable oracle |
|---|---|
| 032 | Distinct array, tuple and struct constants retain two real query calls; zero reuse |
| 033 | `["a:const:str:b","c"]` versus `["a","b:const:str:c"]` retains two calls despite delimiter ambiguity |
| 034 | Equal string literals retain two calls: runtime authority does not prove literal allocation identity |
| 035 | Identical integer payloads with i64/u64 types retain two calls |
| 036 | Redefining receiver, index or cached-result local retains the second read |
| 037 | An admitted runtime length query overwriting receiver/index/result also invalidates reuse |
| 038 | Bare contains/get and unknown user calls remain present and fence cached queries |
| 039 | Consuming Move arguments retain both original calls |
| 040 | Moving the cached result prevents forwarding from the consumed local |
| 041 | Length receiver/result redefinitions invalidate cached length |
| 042 | Aggregate, invalid-local and Move length operands never populate an empty/unsupported key cache |
| 043 | A query writing into its own receiver cannot establish a later equivalent read |
| 044 | A fresh pass retains duplicate rt_array_get and rt_array_len calls without explicit admission |
| 045 | Replacing admission removes previously admitted names and never admits bare get |
| 046 | A duplicate length followed by a consumer redefining the receiver does not skip invalidation; two calls, one reuse |
| 047 | A length destination aliasing its receiver invalidates the next read |
| 048 | Unknown intrinsic and Drop effects fence reuse |
| 049 | Positive/negative floating zero arguments are not collapsed by formatted text |
| 050 | One string argument containing a delimiter does not collide with a two-argument vector |
| 051 | Equal integer constants with the same receiver local yield one call and one copy from the first result |

Cases 032, 035, 049 and 050 exercise conservative canonicalizer input handling,
not validation or execution of those call signatures. Malformed input cannot
serve as a positive execution oracle.

## Existing coverage retained

Cases 001–031 continue covering text pointer identification; legacy method
classification; bare-name non-reuse; admitted runtime array/dict/typed-byte
reads; mutating append barriers; repeated array lengths and consumers; loop
metadata/scalar/bitcast behavior; loop-defined values; typed array index
dispatch; and dead append/write-only arrays versus observed results and known
data-pointer writes. Preexisting fixture correction: scenarios 019, 021 and 022
said queries/scalars/bitcasts stay in-loop but asserted header hoisting and
nonzero counters. They now compare original header/body instruction arrays and
terminators, retain body operations, require an empty header and zero hoist
counters, matching the existing fail-closed implementation. No source change
or executed result is inferred from this correction. Scenario 020 remains the
mutation control.

The pass-level instruction census is stronger than source-shape checks but
weaker than whole-program differential execution. Actual source resolution,
MIR verification, engine parity, callback/error/order behavior, executed
lowering and performance gates remain open. The 51 scenarios are authored
coverage, not 51 passing checks. Regenerate this manual with admitted SPipe
docgen after execution and review all scenario outputs before admission.
