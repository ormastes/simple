# Native runner treats one physical extern provider as competing aliases

Status: production-helper native probe passed all 10 policy groups;
full rebuilt-compiler integration and SSpec execution pending.

Retained probe receipt: `C:/dev/simple-mir-projection-policy-probe-20261025/evidence/terminal.sdn`.
The exact production-helper diagnostic compiled in 30.813 seconds and ran in
0.625 seconds; this does not qualify the full compiler integration.

The provisional pure-Simple producer `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`
compiled the frozen `b66b7b1f78562719ea803d7558300c3d2f054eb0` test-runner source
through a genuine physical checkout projection. HIR completed 288 physical
modules. MIR scheduled 567 logical rows and rejected repeated providers with
identical nonempty physical paths, including `io/dir_ops.spl`,
`fs/host_path.spl`, and `test_runner/test_executor_composite.spl`.

The retained 1,048,576-byte diagnostic contains 1,001 observed conflict records
across 34 observed consumers. Every observed pair has the same literal
provider path. The collector reached its inherited Hello-sized output bound,
returned native status 125, reaped its Job, and reported quiescence. This is an
incomplete failure ledger, not a complete count eligible for manual <=30-file
retry. No object or runner executable was produced. Log SHA-256:
`9cce398af6c3ae68b3196da0b756b358d938c8c9627ee9e3a73dd0101c0f0073`.
Future diagnostic collection uses an 8 MiB bound; diagnostics are not disabled.

The HIR registry deliberately preserves logical `lib.*` / `std.*` lookup
aliases pointing at the same lowered source. The MIR feed copied every lookup
key. Existing physical scheduling excluded projected phase-2 inventories and
bootstrap shortcuts. Streaming parsing retains logical source rows, so equal
source/receipt counts also bypassed that repair.

The repair joins selected source paths to retained full-content admission,
then selects physical source work in selected-source order. Entry position
zero is preserved; retained receipt indexes are never treated as selected
indexes. The logical HIR lookup map remains intact. Provider aliases coalesce
only with the same canonical declaration owner and admitted canonical path,
consistent full-content identities, and equal encoded extern contracts.
Different providers, changed signatures/mutability/effects/attributes, missing
identity, and unsupported contract metadata remain errors. The existing MIR
provenance checker and its pathless bootstrap route remain unchanged.

Contract comparison omits declaration/parameter SymbolIds and top-level
source spans. Existing nested type encodings preserve nominal identities and
type-origin spans. A relocated type origin can therefore conservatively reject
coalescence; the repair does not claim semantic equality for arbitrary relocated
HIR graphs. It never strips type authority or scans function bodies.

A separate operational mistake enabled the interpreter compatibility AST env
mirror in a native producer by omitting canonical
`SIMPLE_NATIVE_ARENA_DECLS=1`. Twenty bounded native samples landed in Windows
environment scans/copies. The canonical bootstrap scripts already set this
flag; the private launch was corrected after the actual 40-function sum-820
compile/run probe passed. This is not a new parser product-code repair and did
not disable Any diagnostics. Original failed/stopped attempts remain retained.

Validation artifacts:

- `mir_projected_owners_spec.spl`: retained/source join, selected order, missing
  and contradictory identities, streaming/native activation cases.
- `mir_provider_aliases_spec.spl`: matching aliases, local symbol relocation,
  conflicting path/type/mutable/effect/ABI metadata and unknown paths.
- `test/fixtures/bootstrap/mir_provider_aliases`: real dual `lib` / `std`
  imports of one physical runtime extern provider; success requires compiling,
  linking and running the generated checksum program.
- Native policy probe executes exact extracted production join/activation
  functions and the actual SHA-256 validator. It does not substitute for
  the typed extern-contract specs or a compiler rebuilt with this repair.

Do not retire this bug or claim the test runner works until the rebuilt
producer compiles/runs the dual-alias fixture and the real runner passes its
positive, deliberate-failure and empty-example refusal calibrations. Whole
suite execution remains separate evidence; zero executed examples never pass.
