# Six compiled subsystem test products

The requested acceptance matrix contains LLVM and Cranelift versions of three
executables: compiler, interpreter and loader. Compiler includes core, HIR, MIR
and the remaining compiler scopes; those are not additional final products.

Discover source owners with:

```sh
sh scripts/bootstrap/compiler-subsystem-test-inventory.shs "$SOURCE_ROOT" > source-specs.tsv
```

This manifest binds each candidate spec file to its SHA-256. It reads the
authoritative unit, integration and system trees, including their `compiler_core`,
`compiler_shared` and `core` sibling roots, excludes fixture/vendor and
legacy mirror trees, and assigns each physical path once: loader first,
interpreter second, otherwise compiler. Repeated backend execution is not extra
source coverage. Suffix-based discovery does not prove that a file registers a
test, nor count generated or conditional cases.

Before running each produced executable, ask that exact binary to enumerate its
registered tests without executing callbacks. Keep its path/hash, provider
identity, raw enumeration and exit status. Execute the same registry afterward;
retain per-case pass/fail/skip and the actual executed count. Unknown or absent
enumeration is BLOCKED, not zero and not an inferred source-pattern count.
An advertised threshold such as 1,000 cases is unproved until binary-owned
enumeration and execution evidence establish it.

Existing `--native-backend=llvm|cranelift` runs build one executable per spec.
The existing test runner's `--list` scans source text. Neither currently supplies
the three aggregate executables with binary-owned registration. The managed
Phase 4 acceptance specs are three-case behavior probes, not full subsystem
suites. Keep those results separate from the six-product matrix.

The separate post-Stage2 product manager schedules each product's build,
binary-owned enumeration and run as dependent operations. A failed build blocks
only that product's enumeration and run; a failed enumeration blocks only its
run. Missing compiler admission blocks that backend's three products while the
other backend continues. The current Linux/FreeBSD budget is 20 build threads
shared by this matrix, with at least 10 per build and the existing enforced RSS
cap. No source suffix count is a registered or executed test count.

`scripts/bootstrap/run-compiler-subsystem-test-products.shs` is the standalone
post-Stage2 entrypoint. It consumes admitted compiler binaries and receipts,
produces six product jobs and an `INCOMPLETE`, `FAIL`, `PASS_WITH_SKIPS`, or
`PASS` matrix receipt. `scripts/bootstrap/verify-compiler-subsystem-test-matrix.shs`
checks a `PASS` receipt against retained binaries, source hashes, raw ledgers,
watchdog receipts and per-case outcomes without executing tests again. These
receipts are separate from canonical Phase 4's three-case acceptance probes.
The manager requires an aggregate product producer and runtime registry; their
source-bound build and native test results remain necessary for six-product
acceptance.

`--mode dynload` controls aspect packaging, whereas `--backend-plugin` selects a
Simple backend provider exporting `simple_backend_plugin_v1`. An LLVM toolchain
DLL or a fallback single binary does not prove that provider was loaded. Report
actual loaded provider path/hash/identity, separately from test counts. C++ test
framework linkage must retain the Simple assertions and share the executable's
registered cases; merely linking a library cannot establish coverage.

This page defines the acceptance boundary and source inventory. The separate
manager scripts supply scheduling and verification only; they do not claim an
aggregate harness, dynamic provider loading, or six passing native products.

## Resume an absent backend without rerunning passed products

Pin the resume-capable manager into the full product source before the first
run. The first run may omit one backend's compiler/admission arguments. Its
three products remain BLOCKED; the available backend can produce three PASS
receipts. The overall matrix remains FAIL until all six products pass.

Once the missing producer is admitted, call the same manager with `--resume`,
the identical source/output roots and resource limits, and both backend
compiler/admission inputs. Resume accepts exactly one fully passing backend
and one wholly absent backend whose nine tasks are BLOCKED. Failed tests,
partial build artifacts, changed evidence or source, changed limits, and
non-admitted producer inputs are rejected. This is not a general retry mode.

An exclusive `.product-owner.lock` covers validation through publication.
A surviving lock after a killed owner requires inspection; never remove it
while its owner is alive. Before changing the journal, resume checks retained
hashes and replays the strict product evidence verifier without executing
native test callbacks. It preserves the old matrix and journal in
`resume-history/`, leaves passing product files untouched, and runs only the
previously absent backend. The existing strict six-product final gate remains
mandatory. Rejected preflight leaves the previous matrix/journal unchanged.
An interrupted resume retains history and is rejected on a second resume;
inspect the partial attempt instead of overwriting it.

Products and their source must remain at their original absolute paths.
Copying evidence to another output root or updating the product source commit
breaks the recorded source, inventory, binary, command and watchdog bindings.
Resume does not establish dynamic backend provider loading: the current product
builder still records builtin provider identity.

## Explicit Phase 2 six-product matrix

Pass `--producer-phase=phase2` to the standalone product manager to build and run
all six products using the admitted Phase 2 LLVM and Cranelift compiler inputs.
No `--product` selector is needed. The owner publishes `producer_phase=phase2`
in the matrix and names its 18 build/enumerate/run tasks `phase2_*`; final
verification and `--resume` require that same phase. Both compiler inputs still
require formal Stage 2 admission and frozen runtime capsule bindings. Source
inventory counts alone never qualify an executable or replace its enumeration
and native execution evidence.

The default remains `phase4` for existing callers. Older matrix receipts lacking
the phase field are interpreted only as legacy Phase 4; explicit empty,
unknown, duplicate or Phase 3 aggregate values are rejected. Phase 3 continues
to require separate managed selected-product tasks. A phase change during
resume, or a journal relabelled to another phase, is rejected even if its outer
hash was recomputed. No native tests are replayed just to validate retained
receipts.

On the 20-vCPU FreeBSD guest, explicitly pass `--threads=20` (the general tool
default is 80), use a fresh product output outside the source root, and retain
the exact product source throughout initial execution and any resume. Bind
`--compiler-llvm`/`--compiler-cranelift` and their producer receipt options to the
actual admitted Phase 2 binary paths; do not replace them with a seed or invoke
an interpreter in place of the six requested native test executables.
