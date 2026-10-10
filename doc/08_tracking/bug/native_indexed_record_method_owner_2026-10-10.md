# Indexed imported-record methods lose their declared owner

Status: **candidate fix; verification pending compiler bootstrap**.

The Phase 4 test-runner closure completed monomorphization (13 templates, 42
calls, 6 specializations, zero unresolved) and visited 217 MIR modules before
reporting unresolved `name`, `is_enforcement_gap`, and `canonical_line` calls
in `compiler/common/assurance/flight_rules`.

## Scoped reproduction

`test/fixtures/compiler/flight_rule_indexed_owner.spl` imports the real registry
and reproduces the same three failures with only two modules. Baseline producer:

`/home/yoon/dev/simple-bootstrap-mir-object-20261011/build/native_probe/combined-fixes/simple`

SHA-256: `67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`.

The native LLVM object build fails in approximately 3.1 seconds at
`flight_rules.spl:503:12`, `flight_rules.spl:514:12`, and the sole
`rules[i].canonical_line()` call at line 525 (the last diagnostic has no span).
The source's direct typed `category.name()` call is not an error. No registry
source was changed and no arbitrary method-name fallback was introduced.

## Candidate mechanism

`flight_rules()` returns `[FlightRuleV1]`. Array indexing records a layout
name for the extracted value, but `remember_array_index_projection_provenance`
previously preserved the declared HIR element type only when that element was
itself an array or slice. Named record elements therefore lost the declaration
that existing owner-qualified method recovery needs.

The candidate keeps the declared HIR element type for every known Array/Slice
projection. Nested-array runtime-handle marking stays conditional; scalar and
record elements do not acquire array storage identity. Callee return signatures
are relocated into the active consumer symbol table before this metadata is
used. The change is confined to the existing projection helper.

The fixture checks real category filtering and gap predicates, then canonical
output including four distinct enum owners that each define `name()`. These
are execution oracles, not merely successful object emission; they have not
yet run with the candidate compiler.

## Evidence and remaining work

Worktree: `/home/yoon/dev/simple-flight-rule-method-owner-20261010`, starting at
integration revision `ee76710f3f2`.

Evidence is under `build/native_probe/flight-rule-owner/`:

- `baseline.log` and `baseline-receipt.json`: reproduced two-module failure.
- `compiler-build.log`: private compiler bootstrap hit its 180-second limit;
  126 cache files were written before the limit.
- `compiler-build-resume.log`: one retry using that same private cache also
  hit its 180-second limit, without a compiler executable. It reached seed
  aggregate-typing admission warnings. Neither timeout was converted to PASS.
- `compiler-cache/`: preserved completed object work for the integration owner.
- `env-working.log`: direct env/runtime guard PASS.

Both bootstrap attempts used the Rust seed only to rebuild the pure-Simple
compiler, with `SIMPLE_NO_STUB_FALLBACK=1` and one compilation worker. The
registry fixture was compiled only by the pure-Simple baseline producer. The
full runner was not rebuilt in this lane.

The integration source also includes the declared-call-result HIR fix absent
from the baseline producer. A new combined compiler should run this fixture
both without and with the projection change when isolating attribution. Until
then, neither independent causality nor native execution of the candidate is
qualified. Keep the scoped cache; do not rerun the unchanged full runner to
investigate this receiver-owner failure.
