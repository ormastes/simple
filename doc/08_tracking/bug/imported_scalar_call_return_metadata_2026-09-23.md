# Imported scalar calls lose return metadata across HIR/MIR

Status: scoped bootstrap scalar-return fix passes the strict native oracle;
full bootstrap qualification remains pending. Base source:
`bbd37e856f65b7a1e086eb60df6764e1da18f912`.

The imported callable surface correctly records `return_type_name=text`.
Registration constructs its Function signature in the importing HIR table,
but expression lowering previously stored only `NamedVar(symbol, name)` and
reached `HirExpr(type_: nil)`. The later MIR table could interpret that same
module-local numeric symbol ID as another module's Bool helper. Rejecting the
foreign name/owner alone prevented Bool corruption but left the existing
return-resolution chain at i64. All 26 path value comparisons passed while
printing 26 pointer integers. Whether a particular registry row was absent
or malformed was not directly decoded; the dropped callee signature and wrong
observable return type are independently established.

The repair carries imported callable Function metadata on NamedVar with an
explicit `has_type_` bit while the declaring signature is available. This is
limited to owner-bearing imported signatures with scalar parameters and return
types (Int, Float, Bool, Char, Str, Unit). It excludes local/parameter function
values and owner-dependent aggregate signatures. MIR uses that bound scalar
return only to recover the resolver's erased i64 result, preserving existing
non-i64 runtime return overrides. Exact name/owner checks prevent a foreign
symbol's Function or HIR sidecar from restoring an unrelated type. No module,
path-normalizer, helper-order, or print-specific type exception was added.

## Native evidence

Worktree: `/Users/ormastes/simple-tmp/imported-callee-return-metadata-20260923`.
Retained evidence: `build/native_probe/imported-return/`.

- Red diagnostic producer SHA256:
  `4f8506de4e96ccc037f6568e3dc72efead96d1a793a6c11ef4a5e805ef7dbfbb`.
  Native build and process exit 0, but exact stdout diff exits 1 with pointer
  integers. This is the prior unaccepted identity-guard candidate, not an
  admitted compiler.
- Final candidate SHA256:
  `af56802dbcfa8aefd5fd29b264cbbcfefcf1aea7417d599a9a26cd4b95b99fe4`.
  Final build and process exit 0; `final-oracle.diff` is empty. All 26 value
  checks and exact text output, including the blank case and marker, pass.
- Final source SHA256: expression_core
  `18894f40e0d06b706567c39e63f2c00145511156938a378ad8fac8cbd0e54cd1`;
  switch_operators_calls
  `7501e6eead0d9a2c404e28654d3c828705adf2f662c5e3f945e7f7b46ed26a83`.
- The bootstrap-only frozen producer SHA256 is
  `da57f073ca4c9217bca520a2867bc3b8e669460043312c82ec00d43f77b1280a`.
  Only a private APFS clone of its cache was written. All 8974 existing object
  hashes remain unchanged. Final incremental receipt: 895 reused / 4 rebuilt
  (two changed modules, canonical entry and assembly sidecar). No shared
  cache or P0 source was modified.

## Bounded cycles and resources

Cycle 1 introduced an extra method, invalidating the global signature key;
the attempted producer was stopped through its watchdog on the 0-cached
receipt. It exited 143, quiescent, before an unrestricted build could finish.
Cycle 2 inlined the identity checks, reused 895 modules, and passed the 26-case
oracle. Independent Astra review then required the scalar/owner restriction,
runtime override preservation and bare-lift assignment used by cycle 3. No
fourth cycle was run.

Final producer: 22.60 seconds, sampled tree peak 1409792 KiB. Final fixture
compile: 11.92 seconds, maximum child RSS 532201472 bytes, sampled tree peak
564672 KiB. Red compile: 12.30 seconds, maximum child RSS 531087360 bytes.
Final execution: 0.32 seconds, maximum RSS 10502144 bytes; red execution:
0.37 seconds, 10616832 bytes. These single observations show no material
regression in this fixture, not a general performance PASS. All final receipts
are quiescent with zero observer errors/restarts under the enforced sampled
5859375-KiB threshold. Sampled protection is not a kernel aggregate limit.

## Remaining scope

This does not implement aggregate/Optional signature relocation, full foreign
symbol-ID safety, or the non-bootstrap symbol fallback. The resolver's i64
answer still conflates an erased fallback with some explicit runtime i64
contracts; no conflicting scalar runtime signature was found in review.
The 26-case native oracle exercises imported text returns, not every scalar
width/ABI or target. General compiler/lib/MCP/LSP suites and full bootstrap
are intentionally outside this isolated diagnostic lane. No source-matched
Stage 2 admission, Stage 3/4 completion, or release PASS is claimed.
