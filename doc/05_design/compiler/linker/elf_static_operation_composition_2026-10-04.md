# Static operational ELF composition

Base: `80b5ab3f6f5`; date: 2026-10-04. Owner: linker_research.
Worktree/session: `C:/dev/simple-item4-elf-composition-docs-20261004`;
branch: `work/item4-elf-composition-docs-20261004`; integration target:
release/1.0. This document owns the approved interface and source-review
contract. Runtime execution and canonical manual generation remain UNRUN.

## Concrete missing behavior

The original linker design requires real facet bindings. At the inspected base
the ELF driver directly invokes layout at `elf_static_link.spl:1503`, relocation
at lines 1654/1657, and image writing at line 1787. No compiler linker calls
`mdsocpp_seal_v1`; the generic IDE pilot is the existing production example.
The generic sealer checks descriptor dependencies and returns slot bindings;
it does not attach those bindings to executable linker functions.

Binding only `reloc_apply` would be ineffective: the following
`reloc_patch_bytes` call independently calculates the emitted bytes. The new
relocation callback therefore returns the byte array consumed by the driver.

## Approved interface

New module: `compiler.backend.linker.elf.elf_operation_bindings`. It imports
`elf_exec_writer`, `reloc_engine`, and generic MDSOC++/KPF model/seal types.
It never imports `elf_static_link` or `ElfLinkRequest`. The driver imports this
module, keeping the dependency graph acyclic.

`ElfOperationProviderV1` contains a `CapsuleDescriptorV1` and these optional
function fields:

| Field | Signature |
| --- | --- |
| `relocate` | `fn(RelocArch, [i64], i64, i64, i64, i64, i64) -> Result<[i64], text>`; arguments are architecture, bytes, offset, relocation type, S, A, P |
| `layout` | `fn([ElfOutSec], i64, i64) -> Result<ElfExecPlan, text>`; sections, base, page |
| `write_image` | `fn(i64, i64, i64, ElfExecPlan, [[i64]]) -> Result<[i64], text>`; ELF type, machine, entry, plan, contents |

`elf_seal_operations_v1(providers, policy)` returns
`Result<ElfSealedOperationsV1, text>`. It appends a fixed engine capsule with
three required facets, validates exact correspondence between offered facets
and available callbacks, invokes the existing sealer, and resolves operations
using its actual provider-slot bindings. Missing, duplicate, and mismatched
operations reject before engine work. A separate caller-supplied receipt is
never accepted as a substitute for this constructor.

`ElfSealedOperationsV1` retains the selected callbacks and its
`MdsocppGenerationReceiptV1` together. Keep fields immutable and module-private
to the extent supported by the language. This is an ownership/API discipline,
not an unforgeable security object: source-level visibility or direct aggregate
construction limitations must be reported honestly. Providers are trusted
in-process functions, not untrusted plugins.

`elf_builtin_operation_providers_v1()` returns the three canonical provider
records for explicit in-process selection. `elf_builtin_operations_v1()` seals
those canonical adapters. Existing `elf_link`,
`elf_link_stripped`, `elf_link_configured`, `elf_link_structural`, and therefore
`elf_static_link` all use that built-in owner while preserving their public
return types. New driver entry
`elf_link_with_operations(req, strip_output, retained_symbols, owner)` returns
`Result<ElfComposedImageV1, text>` with `image` and `composition` fields.

A supplied layout may legally change the image base. The driver's synthesized
header symbols therefore derive their base from the returned header-containing
PT_LOAD segment; they must not retain the original layout argument. Canonical
layout and existing wrapper options retain their established behavior.

## Registry identities and metadata

Capsule IDs use hi `0x4c494e4b45520001`, with lo 1 engine, 2 relocation,
3 layout, 4 writer. Facet IDs use hi `0x4c494e4b45520002`, with lo 1 relocation,
2 layout, 3 writer. Helpers are `elf_operation_capsule_id_v1(kind)`,
`elf_operation_facet_id_v1(kind)`,
`elf_operation_descriptor_v1(capsule_id, provided_offers)`, and
`elf_operation_policy_v1()`. Operation constants are
`ELF_OPERATION_RELOCATE = 1`, `ELF_OPERATION_LAYOUT = 2`, and
`ELF_OPERATION_WRITE_IMAGE = 3`; capsule ordinals are the distinct mapping above.

The canonical policy is Userland, noncritical, one concurrent call, no granted
capabilities, generation 1, and an explicit structural-version digest token.
That token is registry identity, not a digest of function code or an artifact.
Memory metadata declares NoGcGeneral, possible allocation after activation,
alignment 8, capacities 1, and zero reserved byte quantities. The policy's zero
reservation budget checks only those declared reservations.

**Zero reservation means no reserved-accounting claim, not zero memory use.**
No RSS, whole-job budget, absence-of-GC, or hard-bound certification follows.
The resident parser, layout and writer still allocate full objects/images.
UnsupportedBudget admission remains unchanged.

## Runtime result contracts

The relocation adapter performs canonical validation and patching together;
its returned byte array must retain the input length before the driver stores
it. Failure returns no image.

Before using a supplied layout, validate parallel array lengths, section
identity/order and the sizes/flags and ranges required by the driver. Required
section lookups must not become negative indexes. A writer result needs valid
ELF header/length and ranges for subsequent mutations. The driver still applies
RV flags, symbol/attribute sections and final build-id; bounds must cover the
RV header byte and build-id note range before those writes. Shape checks do not
make arbitrary in-process callbacks a secure execution boundary.

Architecture-specific normalization, paired RV ULEB handling, TLS rewrites and
special instruction transforms remain engine-owned. This facet binds the
general relocation-field operation, not every relocation-related action.
The layout facet is normal ELF image layout, not a boot-layout declaration.
The writer facet emits an in-memory image, not transactional file publication.

## Test-first acceptance matrix

| Criterion | Required observable result |
| --- | --- |
| Canonical positive link | Existing default API and explicit built-in owner produce equal real fixture bytes; independently inspect machine, entry and relocation result |
| Selected relocation operation | A supplied operation changes an independently specified relocation field in the emitted image; no fabricated call counter is sufficient |
| Selected layout/writer operations | Real callback results are consumed; named callback errors propagate without an image |
| Structural binding | Receipt provider slots identify the actual selected callbacks, including reordered providers |
| Rejected composition | Missing/duplicate required offers, absent callback and undeclared callback reject before engine dispatch |
| Result shape | Short relocation output, malformed parallel layout arrays/required sections and short writer output reject without unsafe indexing |
| Compatibility | Existing public entrypoints preserve options, stripping and retained-symbol behavior; structural mode is not external execution |

Runtime lane owns the new module and driver integration. Acceptance lane owns
new SSpec/fixtures/manuals, with canonical `std.spec.step` and explicit guards
because matcher failures do not abort. Research owns this design and independent
source review; root owns common ledger/integration. Sidecars: N/A.

## Remaining full-item gates

This closes only the static operational-binding slice when implemented and
verified. It does not implement byte-source operations (parsing bytes is not
input acquisition), all special relocation facets, dynamic artifact trust,
CLI provider selection, complete composition coverage, or bounded execution.
Mapped-provider trust and seals cannot be synthesized from these structural IDs.
Full runtime, compiler, coverage, performance and generated-manual gates remain
separate; no full-item readiness PASS is implied.
