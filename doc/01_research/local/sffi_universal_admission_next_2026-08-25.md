<!-- codex-research -->
# SFFI universal admission: next local research checkpoint

**Date:** 2026-08-25  
**Tree:** `4d11699bc5b`  
**Scope:** owned `src/compiler`, `src/compiler_rust`, `src/lib`, `src/os`, and
SFFI audit tooling; vendor trees excluded.

## Verdict

Simple SFFI is **not globally safe, verified, or signed**. The repository has
useful fail-closed pieces, but no current evidence proves universal production
admission across interpreter, JIT, native, dynload, and SimpleOS.

Do not reuse the 2026-08-23 totals as current-tree statistics. They use an older
scanner and generous file-level unsafe attribution. Newer declaration and call
totals are also historical checkpoints with different units. The source call
census remains a lower bound until resolved-HIR inventory covers aliases,
re-exports, generated calls, methods, and indirect callables.

## Current enforcement boundary

- The normal MIR lowerer rejects non-unit fallthrough with `E-SFFI-016`, but
  bootstrap module lowering still synthesizes zero for non-unit missing returns.
- Typed HIR identifies direct named extern calls and the safety checker finds
  calls outside lexical `unsafe(ffi)`. Default driver severity remains advisory;
  only Critical/Verified deny.
- `raw_sffi_call` remains `allow` in the default lint profile. The declaration
  and call-site ratchets freeze debt but do not verify contracts.
- The audit-only HIR inventory carries no artifact/signature evidence and cannot
  establish production admission.

## Current dynamic-provider boundary

- `ExactArtifactDynLib` provides a Linux immutable snapshot and exact digest.
- `SffiAdmissionReceiptV1` parses bounded canonical text but performs no
  cryptography and is source-forgeable.
- Evidence-bound identity checking compares provider, target, artifact, ABI
  registry, and source-signature closure, then atomically resolves cached i64
  slots. It has no production caller and does not validate loader authority.
- The standalone evidence-admission audit verifies Ed25519 trust, exact inputs,
  ABI closure, artifact symbols, and verification receipts. No compiler/runtime
  loader invokes it.
- Rust `NativeLibManager` and raw `spl_dlopen` load providers without that
  evidence gate. Production Simple callers likewise bypass manifests.
- `FfiManifest.validate_library` checks only symbol presence; it does not prove
  ABI, nullability, ownership, or signing. Its stronger cached resolvers are
  currently unused.

## Ownership and memory findings

`std.sffi.dynamic` is the canonical no-GC synchronous owner and compatibility
modules should export it. `ffi/dynamic_versioned.spl` duplicates the canonical
implementation instead of acting as a facade. `MultiVersionLoader` and
`DynLoader` retain process-global maps without eviction, so provider handles and
path text can remain live indefinitely.

Legacy dynamic calls perform per-call symbol lookup; checked integer transport
also allocates a two-element result array. Cached resolved slots remove repeated
lookup, but remain an unsafe migration ABI restricted to `i64(i64...)`.

## Performance invariant

Admission must be one-time:

```text
immutable artifact snapshot -> hash/signature/trust/ABI/receipt checks
    -> resolve complete symbol closure -> atomically publish cached typed slots
```

No admitted hot call may add hashing, signature verification, filesystem work,
path search, string lookup, dictionary lookup, generic decoding, mutex traffic,
or allocation. Required status/null/descriptor checks remain enabled.

## Statistics contract

Every future count must record tree ID, scanner identity, executable identity,
timestamp, exclusions, and exact unit. Keep these units separate:

- declarations;
- distinct symbols;
- live call sites;
- provider modules/families;
- freshly reverified cryptographic admissions.

States are mutually exclusive per row: `admitted_artifact_bound`,
`unsafe_contract_declared`, `unsafe_or_contract_missing`, and
`unknown_uninventoried`. Backed symbols, source claims, saved receipts, fixture
passes, and immutable snapshots are not “verified” or “signed.”

## Research coordination

Read-only sidecars covered compiler enforcement, library/dynload ownership, and
documentation/evidence consistency. `/root` merged and reviewed the findings.
No full census was rerun in this checkpoint. The canonical release path
identified itself as the Rust bootstrap seed and the focused baseline spec
failed before execution with the already-recorded `function unsafe not found`
defect (`0.79 s`, `190,448 KiB` peak RSS). Repository policy forbids treating
that seed as self-hosted correctness or optimizer evidence, so the criterion was
not rerun and the implementation slice remains unverified.
