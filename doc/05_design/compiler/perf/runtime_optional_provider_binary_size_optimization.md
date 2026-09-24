# Runtime Optional Provider and Binary-Size Optimization Detail Design

## Compile Flow

1. Resolve command, target, architecture, profile, and exact entry closure before runtime/provider initialization.
2. Classify each dependency as base-required, statically demanded, dynamically demandable, or unreachable.
3. Resolve provider selections from metadata and stability receipts without loading implementations.
4. Generate `RuntimeLinkManifestV1`; reject undeclared constructors, exports, archive members, or dynamic dependencies.
5. For release-small, generate `NoUnwindProofV1`. If any requirement is unknown, use ordinary release or isolate the requiring code in a provider DSO.
6. Emit function/data sections with hidden default visibility.
7. Link with target-equivalent section GC, as-needed dependency admission, and optional ICF.
8. Produce unstripped attribution evidence, create a separate stripped artifact, and verify both execute identically.

## Loader Flow

1. A capability call resolves its metadata-only provider slot.
2. The slot verifies policy generation, ABI, target, architecture, artifact digest, dependency closure, and stability state.
3. The loader maps only the selected sealed artifact and required dependencies.
4. Initialization is bounded to declared provider hooks.
5. The slot publishes atomically; waiters share the result.
6. Failure returns a typed capability error and cannot trigger an undeclared fallback.

## Pure-Simple Dual Mode

Every dual provider uses the same public Simple trait and normalized error model. Selection is external to callers. Shadow execution is forbidden for filesystem writes, network sends, database mutation, randomness, clocks, process control, UI effects, and hardware operations. Those providers use replay fixtures or offline differential tests instead.

Promotion requires:

- full functional and mutation coverage;
- architecture matrix;
- normalized error/failure parity;
- p50/p95 latency and RSS;
- startup dependency proof;
- no direct foreign fallback in pure-Simple code;
- rollback artifact retained for one release window.

## Size Attribution

For Simple and same-toolchain C hello, retain:

- unstripped and stripped bytes;
- segment/section table;
- top symbols by size;
- linker map and removed-section report;
- archive members extracted and why;
- exports, constructors, dynamic dependencies, relocations, and unwind/RTTI sections;
- runtime feature-closure receipt;
- checksum-equivalent output and exit status.

The gate fails if unexplained bytes exceed 1 KiB or if any optional provider appears.

## No-Unwind/No-RTTI Admission

The proof rejects release-small when any selected object:

- throws or catches exceptions;
- permits foreign exceptions across SFFI;
- requires cleanup landing pads;
- requests stack-unwind backtraces;
- uses RTTI, dynamic casts, virtual registration requiring RTTI, or exception personalities;
- retains `.eh_frame`, `.gcc_except_table`, LSDA, personality, typeinfo, or unwinder dependencies without a target ABI justification.

Post-link scanning is mandatory; compiler flags alone are not proof.

## Tests

- No-import hello loads no optional providers.
- Each optional capability loads exactly its selected provider and no sibling.
- Wrong ABI/digest/architecture/dependency rejects before mapping.
- Pure/foreign provider parity and rollback.
- Effectful providers never shadow execute.
- NoGC no-allocation hello contains no collector symbols/init.
- Release-small no-unwind closure and injected unwind/RTTI mutation rejection.
- C-relative size gates for debug, unstripped release, and stripped release-small.
- All supported architectures retain feature availability through on-demand provider tests.
