# Imported primitive fields trigger false re-export advisories

Status: OPEN. Severity: P2. Source repair and six compiled-only HIR cases are
AUTHORED_UNEXECUTED; the three-module native fixture is UNEXECUTED. No release
runtime admission or measured wall-time improvement is claimed.

## Actual evidence

The live b58 Phase3 attempt uses producer
`892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`,
source `b58baa89e4d65a40768fceaf8221fdbdbe58da24`, and SCV revision
`841113c04c75872ad2886e959134da2529f209b8cc8d23f0e33fb3118ceb8ae6`.
The bounded 9,987,373-byte log prefix contains 14,259
`hir-reexport-chase-unresolved` messages, including 10,281 primitive-name
occurrences. It contains no `E-HIR`, `HIR aggregate failure`, `failed_modules=`
or `error:` marker. These are advisory occurrences, not failed modules or a
terminal build verdict. Repeated diagnostics obscure progress; their share of
build duration is unmeasured.

Evidence: `b58-hir-primitive-reexport-advisory-diagnosis.json` under
`/mnt/c/Temp/simple-phase2-cuda-owner-20261011`, SHA-256
`f92cc4409dc0c3c52a1ae25d93f988ab447d50e470ef5f35062064582e1c8809`.
The two resolver files and three backend witness files are byte-identical in
that snapshot and release `226d6963aa9e59a97d0db219553a15394c38650f`.
This repair starts directly from that release, with no b58 history transplant.

## Cause and change

Imported composite fields call `materialize_imported_field_dependency_inner`,
which registered primitive names against their declaring module without the
builtin filter already used by callable and enum-payload dependencies.
A module cannot declare the canonical primitive `i64`, `u8` or `text`, so the
search reaches the unconditional re-export advisory. The wasm adapter correctly
imports backend types; adding primitive imports there would not repair this.

After validating the physical owner and generation, apply the existing
`hir_dependency_is_builtin_type(hir_dependency_type_name(dependency))` policy
before qualified lookup and registration. This also handles `has_i64` optional
sugar. Keep declared aliases, nominal names and all existing resolution/error
paths. In particular `Option`, `Result`, `Dict` and capitalized `Bool` may be
user declarations and must not be filtered. This is a dependency traversal fix,
not diagnostic suppression or a general missing-type fallback.

## Reproduction and prevention

- `test/fixtures/compiler/hir_primitive_field_dependency/{owner,facade,main}.spl`
  imports a record through a facade and checks actual scalar, byte-array, text,
  boolean and optional values. Future native qualification requires expected
  run exit 0 and absence of primitive re-export advisories in the compile log.
- `test/01_unit/compiler/hir/imported_primitive_field_dependency_spec.spl`
  uses parsed module surfaces and the real HIR owner. It checks zero re-export
  search calls for primitives (the path emitting the warning), successful full
  imported-field lowering, exact foreign/alias owner binding, user-defined
  container-name registration, retained MissingPayload diagnostics, and invalid
  owner rejection before filtering. Six real scenarios; no source-text oracle.

Runtime execution awaits a qualified release-built full CLI and serialized
native slot. Require six executed cases, zero failures/skips, plus the native
fixture's real object/link/run evidence. Static checks and source review do not
replace those gates; do not relabel this report FIXED until qualification.

Related prior policies:
[owner dependency diagnostics](hir_unresolved_type_owner_missing_import_2026-08-22.md)
and [container origin search storms](hir_builtin_container_origin_search_storm_2026-08-22.md).
