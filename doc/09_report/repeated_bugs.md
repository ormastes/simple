# Repeated bootstrap lowering bugs

Updated: 2026-10-09. This report distinguishes repeated module failures,
confirmed source fixes, unverified repair candidates, and executable evidence.

## Evidence and scope

Release baseline: `fcf72be25d3d9a561db9915b41227b0c106df96f`.
The active Phase 3 diagnostic run uses source
`6bf3276a4344923bea1dae84c933b2aeda13db58` and compiler SHA-256
`b467f5212ff1d937d93c78cf23e313c27bfb5a29dd9bf1c2baa567edffc442e2`.
It therefore cannot verify fixes merged after that compiler was built.

The reviewed snapshot contains 251 newly completed attempts, excluding 847
carried results: 240 compile failures, seven unqualified COFF objects, and four
measurement failures. These are historical snapshot counts, not final totals.
Failure categories overlap. A module importing a broken shared component can
repeat its diagnostics; a failed module is not necessarily a distinct bug.

Local evidence:

- `build/native_probe/phase3-failed-only-review-20261009/REPORT.md`
- `build/native_probe/phase3-failed-only-review-20261009/release-fix-map-20261009.md`
- `build/native_probe/phase3-failed-only-review-20261009/worker-access-violations.json`
- `build/rc1-test-products-preparation/retry-20261009/release-mir-applicability-20261009.md`

## Repeated failure families

| Family | Evidence | Release/source status | Required prevention |
|---|---|---|---|
| Array element loses nominal struct ownership | 43 for-in/I64 signatures; 31 name the Windows process owner and `state.pins` | `431967d30a2` repairs global Array/Slice element provenance; current producer predates it | Global and local arrays, indexed element fields, nested arrays, empty arrays, unrelated scalar negative controls |
| Text receiver loses its actual type | 49 unresolved-method signatures, including `contains`; old source locations are unreliable | `f87ed657830` and `cb2bed7ddff` add relevant optional/indexed text handling and nil rejection; not proof that every method failure is fixed | Indexed record fields, optional Some/empty text/nil, chained methods, and array receivers that must not become text |
| Imported nested enum becomes a struct-like value | Repeated `ProcessObservationPacketKindV4` operator errors | Private candidate `a3564f30bef` is absent from the release baseline; integration under review | Provider-owned nested fields, colliding nominal names, nested imports, and non-enum fields |
| Direct-call result loses enum ownership | Declaration return type can be more precise than the lowered temporary | Private candidate `fc4d105bd68` is absent from the release baseline; integration under review | Enum, record, scalar, and optional returns; unresolved declarations must not acquire guessed enum types |
| Bare variant is resolved without its subject enum | Unsupported match-arm patterns recur across imported closures | Private candidate `a1cfad68e8d` is absent from the release baseline; integration under review | Same variant spelling in unrelated enums, qualified and bare variants, payload variants, valid bindings, and invalid qualified variants |
| Unsupported inferred arm type | 33 signatures in the reviewed snapshot | `20ef5f9528a` improves diagnostic ownership; it does not implement missing lowering | Assert both the unsupported construct and accurate module/function attribution |
| Native worker access violation | 51 child-worker crashes after monomorphization, entering module MIR lowering | No common root cause established | Preserve individual crash reproductions, process closure, and memory evidence; do not classify every crash as the enum bug |
| Verifier failure | Five signatures in the snapshot | Not established as repaired | Keep verifier rejection enabled and reproduce the exact invalid IR |

## Why these bugs appear repeatedly

1. Shared dependencies spread one failure across many entry modules.
2. HIR-to-MIR and provider boundaries can lose nominal owner information.
   Reconstructing it from field spelling or global variant uniqueness is unsafe.
3. Existing long-running compilers retain their old implementation after source
   fixes land. Source presence, a merged PR, and a rebuilt executable are
   different states.
4. Old diagnostics sometimes name an enclosing constant or function rather
   than the failing expression. Similar messages are not sufficient proof of
   a shared root cause.
5. A passing interpreter/spec check does not establish native lowering,
   linking, runtime ABI, or both-backend correctness.

## Repair and regression rules

- Carry declared nominal ownership across imports, fields, indexing, and calls;
  use explicit declaration/provider evidence rather than guessing a type.
- Resolve a bare enum variant against the known subject enum. A variant in an
  unrelated enum must not capture a legitimate binding with the same spelling;
  preserve the language's binding rules and reject invalid qualified variants.
- Pair every positive reproduction with a nearby negative or ambiguous case.
  Include scalar, record, optional, array, and enum boundaries as applicable.
- Check the Rust seed counterpart for the same semantic hazard, while keeping
  seed diagnostics separate from pure-Simple native qualification.
- Do not fix a compiler error by changing source tests to pass, suppressing the
  verifier, introducing stubs, or weakening source/cache identity checks.
- For performance changes, preserve byte identity, error order, ownership, and
  invalidation behavior. Measure peak memory as well as elapsed time. Native
  text-array join is not a safe canonical-encoding replacement when it truncates
  embedded NUL; test that case explicitly.

## Verification and application sequence

1. Review and compose the enum fixes against the pinned release baseline.
2. Add focused `.spl` reproductions and similar-case negative regressions.
3. Run the available focused checks and record their exact runtime/producer.
   Mark unavailable tests UNRUN; do not infer PASS from test-file existence.
4. Build a separate successor with valid source/runtime/cache identities and
   pass its compiler sanity checks before replacing a running producer.
5. Retry representative failed modules first, preserving compatible caches and
   prior passing evidence. Verify LLVM and Cranelift separately where affected.
6. Compile, link, and execute affected test products. Record registered,
   executed, passed, failed, and skipped counts separately.
7. Update this report with actual commits and results. A fix is source-landed,
   producer-built, or native-verified; never use those states interchangeably.

## Current repair status

Enum identity/provenance and subject-bound variant repairs are being reviewed
in separate lanes. Their new tests and composed implementation are not yet
qualified. Existing array/text fixes are on release but are not in the active
Phase 3 producer. No claim is made that all lowering failures or worker crashes
are fixed.
