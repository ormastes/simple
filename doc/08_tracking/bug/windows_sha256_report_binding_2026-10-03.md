# Windows SHA-256 report method binding

Status: source mitigation proposed; native verification UNRUN.

The Windows resume2 phase3-16 compilation of
`src/app/bootstrap_builder/native_group_linux_launcher.spl` reports
`unresolved method call: verified at src/lib/common/crypto/sha256.spl:24:9`.
Evidence is recorded in
`D:/dev/bootstrap-failure-catalog-20261002/windows-resume2/evidence.json`;
the log is under
`D:/dev/windows-release-7734-build-20261002/phase34-diagnostic-resume2/phase3/llvm/modules/work/attempt.uEL7zD/16/compile.log`.
The frozen failed source is `7734f947be8ba9465d0ba312170681074e990587`.

At candidate `00b1923fe2e624a26c6b3f1534327d21efc41a83`, five inferred
locals in SHA-256 receive `SecureZeroReport` from an imported function, but
the module imports only that function. Each then calls `verified()`.
The existing native SHA-256 regression explicitly imports and annotates
`SecureZeroReport` for its equivalent direct call. This change gives the
five production locals the same explicit binding. It retains every volatile
wipe, readback, and fail-closed check; no cryptographic arithmetic changes.

Compiler debt remains: a function's declared return type should suffice to
resolve methods without this explicit import/annotation. The precise compiler
inference failure is unproven until an isolated before/after native reproduction
is admitted. The diagnostic line is not a precise call-site locator.
This is a bounded source mitigation, not a claim that the compiler is fixed.

The existing `sha256_method_binding_main.spl` fixture retains fixed SHA-256
vectors and actual wipe readback, and now checks streaming zeroization,
every state/block/schedule slot, and rejection of updates after zeroization.
Native compilation and execution must both succeed and print
`SHA256_METHOD_BINDING_NATIVE_PASS` before marking this failure resolved.

Runtime verification is UNRUN: the parent requires resource admission before
new compiler/native/WSL jobs. No build or cache was started or modified.
The contracts.lower failure and all other inventory failures remain open.

## Astra source review, 2026-10-03

The recorded phase3-16 log contains five `verified` MIR diagnostics at the
same synthesized SHA-256 location (lines 999-1003), consistent with the five
production calls. It does not establish which compiler mechanism failed.
At candidate `b1ba03bc70b5517619875861f489da0c5fd56b33`, imported free functions
already materialize signature dependencies and retain their callable types
(`module_import_registration.spl:687-702`, `module_callable_types.spl:385-425`,
under `src/compiler/20.hir/hir_lowering/_Items/`). Return-type dependencies
are handled by `module_reexport_materialization.spl:1209` in that directory.
Consequently, lack of an explicit type import is not itself a demonstrated
compiler defect. The mitigation supplies a direct local type and type import;
the MIR unresolved-method recovery consults receiver provenance and the
owner-qualified method registry (`src/compiler/50.mir/_MirLoweringExpr/` +
`method_calls_literals.spl:3356-3400`). Native before/after evidence is still
required; no compiler change was made on the basis of source inspection.

The first streaming regression fed only one byte, leaving every schedule slot
at its initial zero value. That could miss a skipped schedule wipe. The fixture
now fills every state/block/schedule slot with a nonzero sentinel and checks
each write before zeroization. It also asserts the exact buffer sizes before
and after the wipe, reset counters, finished state, and reuse rejection.
This tests the wipe independently of schedule expansion; it does not claim a
new streaming digest vector. Runtime validation of these checks remains UNRUN.

For native proof, first admit a self-hosted producer by exact binary hash,
phase, frozen source and supported command. Build this fixture with
`SIMPLE_NO_STUB_FALLBACK=1`, a single worker, the smallest source-authoritative
entry closure, and a dedicated cache keyed by phase, producer hash and closure.
Retain compile and run logs; require exit zero and the exact PASS marker.
Compare against the pre-mitigation SHA-256 source using a separately bound
closure/cache, then verify the original failing launcher closure. A green
fixture alone does not prove the broad launcher failure resolved. The rejected
7734 diagnostic Stage 2 is not an admitted producer, and current resource
admission still prevents any native build. No guard was lowered or cache changed.
