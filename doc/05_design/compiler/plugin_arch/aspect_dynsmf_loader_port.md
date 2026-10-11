# Aspect dynSMF loader port V1

Status: DESIGN CANDIDATE. The kernel closure audit still reports two K0-to-OS imports in `src/compiler/99.loader/module_loader_compat.spl`. This document is a repair plan, not an implementation or verification claim.

## Current owner and boundary

`ModuleLoader.aspect_owner` is a reference-semantic class. Its private V3 rows bind the facet pin, dynSMF query, execution leases, close reservation, native release attempt, and retry/ack state. The methods in `module_loader_compat.spl` serialize logical transitions with `aspect_lifecycle_gate`. The OS owners retain the physical query and mapping receipts. The loader's final-unpin flow leaves the logical gate before native release, then reacquires it to commit the result.

The two direct imports provide five operations from `os.smf.dynsmf_owned_v2` and three from `os.smf.smf_dynlib`. The operations include query admission, observation, ordinary query drain, close reservation, physical release attempt/observation, close commit, and acknowledgement. Moving the entire compatibility loader to a plugin would move the K0 aspect host and hide the architectural violation, so it is not the selected repair.

## Port contract

A K0-owned typed port carries the minimum operations and result records needed by the loader. Handles remain opaque; callers cannot construct a successful release or supply physical mapping receipts. The trusted OS adapter translates port calls into the existing OS owner operations and returns only observations tied to owner-retained rows. The port must preserve these invariants:

1. Query admission occurs after an aspect pin and must be rolled back with that pin on any later binding failure.
2. Close reservation makes the exact library Closing before native release; only the final query can reserve it.
3. Native release runs outside the logical gate and is serialized by the physical owner.
4. Recovery observes the retained native attempt after a lost completion gate. Retry reuses the same attempt identity and does not free a segment twice.
5. Logical dynSMF commit accepts the retained close reservation plus retained attempt; aspect commit and native acknowledgement happen in that order.
6. All failure and retry paths leave one authoritative owner row, including copied `ModuleLoader` values.

The composition root may install only the fixed OS adapter using an owner-issued issuer capability. A public callback registry or caller-provided release result would allow a fake physical completion. Before enabling dispatch, the implementation review must prove the language-enforced issuer boundary. If that proof is unavailable, dispatch stays unavailable and the two imports remain an explicit open violation.

## Implementation and evidence sequence

1. Define port request/result types in K0 with opaque handle wrappers; no caller-supplied physical-success result can authorize a commit. Keep native mapping receipts in the OS owner.
2. Prove the private issuer mechanism with a negative fixture: an ordinary package cannot install a fake adapter or forge a successful close.
3. Bind the OS adapter in the trusted composition. Preserve the lock ordering A(loader), B(library), C(facet) and the release outside the logical gate.
4. Replace the direct imports in `module_loader_compat.spl` with port calls. Do not change the kernel manifest to make the two edges disappear by reclassification.
5. Run `check-kernel-closure.shs` and the V3 final-unpin authority spec, including copied-loader, in-flight completion, failed native release, explicit retry, and stale handle cases.
6. Run the core runtime and MCP native smoke gates required for compiler changes, then measure no-import startup, representative request p95, and peak RSS against the admitted baseline. Apply the shared normalized-sum rule and independent budgets.

Until all evidence passes, Item 5 remains open and release landing is blocked.

## Closure and SOSIX constraints

A named `use lazy app.startup.dynsmf_status.{run_product_dynsmf_status}`
would still collect `dynsmf_status` in the native entry closure. The
self-hosted scanner explicitly treats named lazy imports as static name
dependencies in `src/compiler/80.driver/driver_source_loading.spl`. Replacing
the current import with that spelling is therefore not a size cut. A real
first-demand path must defer the compiled provider artifact itself and prove
that the default entry's link map and loaded-image list exclude it.

The [SIMD/GPU/SOSIX design](../simd_gpu_sosix_variation_final_2026-10-10.md)
keeps artifact identity, trust, ABI admission and dependency policy in the
loader. SOSIX owns native mapping and dynamic-library mechanisms. The port
must maintain that split: its logical V3 rows stay with `ModuleLoader`; the
physical adapter delegates only host effects through SOSIX and retains exact
mapping receipts in the physical owner. A wrapper that merely renames an
`os.smf` import to `os.sosix` without this route and lifetime proof does not
close the boundary.

The current OS helper functions have underscore names but are directly imported
by the K0 loader. Naming and an `export` list alone are not proof of a
language-enforced private issuer. The negative fixture in the sequence above
must compile a hostile importer and show that it cannot install a fake adapter
or authorize a physical success; until then the port remains a design candidate.

The default dynSMF manifest already marks its file, network, renderer, UI and
tool entries `default_autoload: false` in
`src/os/smf/dynsmf_session.spl`. Repeating that metadata edit would not remove
any static entry-closure code or mapped library. The next implementation cut is
the artifact/command boundary: the no-import entry must link only its static
bootstrap mechanism; a requested feature must admit and bind its separately
compiled provider on first demand, with link-map and loaded-image evidence for
both paths.
