# Item 3: canonical builtin dispatch identity candidate

Date: 2026-09-29. Owner: Codex items3_7 parallel lane.
Status: incomplete, diagnostic failures retained. No production PASS.

## Actual prerequisite addressed

Builtin Array map/filter calls previously reached MIR as unresolved calls;
the logical collection extractor requires operation identity. The candidate
adds an appended HIR builtin-resolution variant with ArrayMap and ArrayFilter
operations, updates resolver/provider transport and exhaustive consumers,
and connects that identity to actual MIR dispatch. The builtin fallback runs
after instance, trait, and UFCS resolution. Named user classes do not acquire
builtin identity merely because they expose a method called map.

The classifier requires a typed Array, one positional argument, and a unary
inline lambda; filter additionally requires no captures, matching its
existing native callable surface. This is bounded dispatch recognition,
not proof of callback purity or result-type correctness. No fusion,
algorithm selection, fabricated symbol ID, or empty advisory registry was
introduced. Untyped flat-bootstrap lowering retains its original path.

The HIR interpreter candidate executes map/filter via the existing closure
call owner and validates filter boolean results. Its filter result evidence
is currently failing and must be resolved before acceptance.

## Schema/cache evidence

The canonical pure-Simple command
`run src/app/compiler_schema/main.spl codec build/native_probe/item3-codec`
completed with exit 0 and 97 reachable declarations. Its generated output was
copied to `src/compiler/20.hir/generated/hir_codec.spl`; no generated arms
were hand-edited. Existing MethodResolution tags 0 through 4 are unchanged;
BuiltinCollection is appended at tag 5.

Ordinary codec version changed from `spl-hircodec-v2` to `spl-hircodec-v3`;
canonical version changed from `spl-hircodec-canonical-v1` to
`spl-hircodec-canonical-v2`. `driver_hir_cache.spl` includes the ordinary
header in keys/entry headers; portable object identity derives from the
canonical codec identity. A real typed module byte-roundtrip and rejection
of a replaced old header passed in the Phase 1 integration diagnostic.

## Bounded TDD

Runner: authorized Windows Phase 1 seed, SHA256
`6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
Spec: `test/02_integration/compiler/collection_builtin_resolution_spec.spl`,
`--mode=interpreter`. These are seed diagnostics, not admitted self-hosted,
native executable, WSL, or performance evidence.

| Cycle | Outcome |
|---|---|
| Red, original owner | 1 example, 0 passed, 1 failed: resolved identity absent. |
| Candidate identity/schema | 2 examples, 2 passed. |
| Extended MIR/interpreter coverage | 3 examples, 1 passed, 2 failed. |

Cycle 3 failures:

- MIR lowering returned zero errors, then the test failed because
  `serialize_mir_module` was not imported from `compiler.mir.mir_serialization`.
  Emitted instruction assertions did not execute.
- Interpreter map produced expected 5; filter produced a shape not matched
  as `Value.Int(2)` (test sentinel -1). Root cause remains unproven.

Logs: `C:/Users/User/dev/simple-item3-identity-red.log`,
`C:/Users/User/dev/simple-item3-identity-cycle2.log`,
`C:/Users/User/dev/simple-item3-identity-cycle3.log`, and
`C:/Users/User/dev/simple-item3-codec.log`.

No fourth verify/fix cycle ran. Item 3 remains incomplete: the real driver
quiet-resolver path is still opt-in, registry/extraction integration is
unfinished, and the required cross-engine/NFR/self-hosted gates have not passed.

## Diagnostic manual generation (2026-09-30)

The same Phase 1 runner generated the mirrored manual without executing the
capped integration tests. It reported one complete document and zero stubs,
but also seven authoring warnings: short introductory documentation, missing
Overview/Description and Syntax/Examples sections, and missing requirement,
plan, design, and research links. The generated scenario steps and folded
source were inspected. Zero stubs does not establish manual-quality acceptance;
that gate remains open along with admitted docgen/maintenance and execution.
Log: `build/native_probe/index-compatibility-tdd/item3-docgen.log`.

Independent read-only review also identified filter contract gaps: admission
does not constrain Array element type or prove a boolean callback result;
the existing MIR filter path decodes i64 and treats a nonzero callback result
as true, while the candidate interpreter requires Value.Bool. This is an
additional acceptance blocker, not a diagnosed explanation for the sentinel
failure. No source correction or test rerun followed the cycle cap.
