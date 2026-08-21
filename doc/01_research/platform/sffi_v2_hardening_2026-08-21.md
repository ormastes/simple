<!-- codex-research -->
# SFFI v2 Hardening Research

**Date:** 2026-08-21

**Assessment baseline:** `2624da57f05e7ad1865b56493bbcb3a04e2b0dd3`

**Status:** Research synthesis and normative direction; no implementation claim

## Executive finding

The current SFFI boundary is not fail-closed. Missing Simple returns and several
foreign-call failures can become plausible values (`nil`, zero, `false`, or
empty data), while the generic dynamic dispatcher cannot represent the declared
ABI safely. SFFI v2 must make compiler-owned typed contracts authoritative and
permit each call to produce only a contract-valid typed value, `Option.None`, a
typed `Result.Err`, or a fail-closed admission error.

The recommended boundary is:

```text
C / C++ / Rust implementation
    -> versioned stable C ABI shim
    -> generated raw SFFI declaration (always unsafe(ffi))
    -> generated validation/lift wrapper
    -> safe Simple API: T / Option<T> / Result<T, SffiError>
```

## Repository findings

### Missing returns are conflated with `nil`

The interpreter function-execution choke point handles a body with no produced
value as `Value::Nil`. Its later `validate_unit!` guard validates unit returns,
not every declared return type. A non-optional `text`, resource, struct, or
other `T` can therefore receive a value that its contract does not permit.

Required semantic outcomes:

| Outcome | Required result |
|---|---|
| Unit-returning function falls through | `Unit` |
| Explicit optional absence | `Option.None` |
| Non-optional `T` falls through | `E-SFFI-016` / missing return |
| Foreign non-null contract returns null | typed contract error |
| Nullable foreign contract returns null | `Option.None` |
| Symbol or ABI resolution fails | typed SFFI error |

Hardened profiles should also reject accidental optional fallthrough; absence
must be explicit.

### The generic dynamic dispatcher is ABI-unsafe

The current dynamic path converts `Nil` and unsupported complex values to zero,
leaks temporary C strings, transmutes every function to an all-`i64` signature,
treats every return as `i64`, and can return zero for null function pointers.
This is not repaired by checking `result != 0`: floating-point conventions,
aggregate layout, descriptors, ownership, callbacks, nullable pointers, and
architecture-specific return rules remain wrong or undefined.

Hardened execution needs generated per-signature thunks. A genuinely open
development plugin may use a complete libffi-style descriptor path, but only
inside explicit `unsafe(ffi)` and never in critical mode.

### Existing analysis is an inventory, not an authority

Textual `rt_*` discovery cannot prove resolved symbol identity, calling
convention, layout, ownership, nullability, unwind behavior, or that analyzed
source produced the loaded binary. One compiler-owned typed ABI registry must
drive the interpreter, JIT, native/AOT, dynloader, SimpleOS loader, binding
generator, and conformance tests.

### Unsafe capability and artifact assurance are incomplete

Simple has the canonical `Ffi` unsafe capability, but historical compiler lanes
have not enforced one consistent lexical boundary. Every raw foreign call must
lower to one HIR operation carrying `UnsafeCapability.Ffi`.

Existing assurance stamps and artifact manifests are useful foundations, but a
deterministic text fingerprint is not a cryptographic artifact identity, and a
signature field is not admission without a canonical signed message, trusted
key registry, parser, revocation policy, and loader-side verification.

### Existing repository guidance needs a v2 correction

The current SFFI guide accurately recommends wrapper layers and `Result`
handling, but still presents raw `i64` handles and direct raw calls as ordinary
patterns. SFFI v2 must distinguish an unvalidated foreign value from a safe
Simple value and make ownership, allocator, nullability, and status semantics
executable metadata rather than documentation alone.

## Contract model

Each non-unit foreign function must declare exactly one return family:

- `infallible_value(T)` (trusted or proof-admitted only)
- `nullable_value(T)`
- `status_only(Status)`
- `status_out(Status, output, success_values, output_contract)`
- `sentinel_value(T, invalid_values)`
- `tagged_result(tag, payloads)`

Type selection follows semantics:

| Foreign behavior | Safe Simple type |
|---|---|
| Null forbidden | `Result<T, SffiError>` |
| Null means ordinary absence | `Option<T>` |
| Failure plus optional success value | `Result<Option<T>, SffiError>` |
| Status plus non-null output | `Result<T, SffiError>` |
| Borrow valid only during call | copied value or scoped borrow |
| Owned pointer | resource with generated destructor |
| Unverified pointer/descriptor | remains inside `unsafe` |

Every pointer/resource output also needs ownership metadata: borrowed scope,
owned release symbol and allocator domain, shared retain/release policy, static
lifetime, or opaque handle sentinels. Unknown ownership is unsafe-only.

## Provider ABI and admission

C++ implementation details stay behind `extern "C"` shims that catch exceptions
and translate them to status values. Rust exports only C-compatible fixed-layout
types and status/out APIs; ordinary Rust `String`, `Vec`, references, trait
objects, `Option`, and general `Result` are wrapper-level types, not the stable
cross-language ABI.

A sealed provider is admitted atomically:

```text
open immutable artifact
 -> hash exact bytes
 -> parse bounded canonical manifest
 -> verify trusted signature
 -> validate target and policy
 -> validate ABI registry and evidence
 -> resolve every required symbol
 -> cache typed function pointers
 -> publish provider
```

The hot path then contains only a cached typed call, status/null/sentinel checks,
descriptor checks where required, and typed lifting. It performs no hashing,
signature verification, library search, symbol-name lookup, registry-map lookup,
or generic marshalling.

## Evidence model

No single analyzer proves arbitrary foreign code correct. Evidence remains
obligation-scoped and bound to exact build identities.

| Layer | C/C++ | Rust | Establishes |
|---|---|---|---|
| Diagnostics | Clang nullability, SAL, static analyzers | compiler lints, unsafe inventory | likely declaration/dataflow defects |
| Dynamic | ASan, UBSan, fuzzing | Miri, fuzzing | exercised memory/contract defects |
| Bounded proof | CBMC | Kani | properties within models and bounds |
| Deductive proof | ACSL + Frama-C WP | contract-specific proof tooling | stated obligations under assumptions |
| Supply chain | SHA-256 + signed provenance | same | exact identity, not semantics |

Attributes such as `returns_nonnull` must never replace validation: when false,
they may introduce undefined behavior and allow optimizers to remove checks.
Potentially null pointers are lifted with a checked operation analogous to
Rust's `NonNull::new`.

## Hash and signature separation

SFFI evidence needs distinct SHA-256 identities:

- `canonical_source_tree_sha256`: reviewed text with CRLF/lone-CR normalized to
  LF, manifest paths normalized to `/`, paths bytewise sorted, and entries
  length-framed;
- `exact_build_input_sha256`: exact generated/preprocessed compiler inputs;
- `artifact_sha256`: exact binary bytes, with no normalization;
- compiler artifact and compiler source-tree hashes;
- ABI registry and verification-report hashes.

The signed `SffiEvidenceManifestV1` binds provider/target identity, all source,
compiler, dependency, flag, registry, artifact, and receipt hashes, plus builder,
validity, and revocation metadata. Signing authenticates identity and provenance;
it does not prove nullability, memory safety, or ownership correctness.

## Assurance policy

| Provider state | Raw call | Safe wrapper | Critical admission |
|---|---:|---:|---:|
| Unknown/unsigned | explicit unsafe development only | no, except copying/sandbox adapter | no |
| Signed, semantically unverified | unsafe internally | only wrapper-established invariants | no by default |
| Analyzer/sanitizer/test evidence | unsafe internally | narrow opaque/status/copy APIs | policy-dependent |
| Formally verified or isolated, exact artifact sealed | hidden in generated wrapper | yes | yes after admission |

When in-process lifetime, aliasing, bounds, or memory-safety obligations cannot
be established, use a capability-limited helper process or Wasm component with a
validated serialization protocol. A signature or null check does not make an
arbitrary in-process provider memory-safe.

## Immediate decision

P0 must precede any claim that current SFFI is non-null-safe or mission-critical
safe. It must reject non-optional fallthrough, remove zero/nil extern fallbacks,
reject missing symbols and null function pointers, disable the all-`i64`
dispatcher in hardened lanes, remove weak fabricated providers, and add
cross-lane sabotage fixtures.

## Research references

- Rust RFC 3484, *Unsafe extern blocks*: https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html
- Rust `NonNull<T>`: https://doc.rust-lang.org/std/ptr/struct.NonNull.html
- Clang attribute reference: https://clang.llvm.org/docs/AttributeReference.html
- Frama-C WP: https://www.frama-c.com/fc-plugins/wp.html
- CBMC function contracts: https://diffblue.github.io/cbmc/contracts-function-contracts.html
- Kani function contracts: https://model-checking.github.io/kani/reference/experimental/function-contracts.html
- RustBelt: https://plv.mpi-sws.org/rustbelt/popl18/
- Git attributes and EOL normalization: https://git-scm.com/docs/gitattributes.html
- SLSA provenance v1.2: https://slsa.dev/spec/v1.2/provenance
- WebAssembly Component Model canonical ABI: https://github.com/WebAssembly/component-model

## Research provenance

This document preserves and repository-aligns the supplied SFFI assessment.
Local code/repository findings were originally inspected at the stated baseline;
paths and implementation facts must be revalidated immediately before P0 edits.
Sidecar lanes: `N/A` for this document-preservation task. Final synthesis and
scope review: primary Codex agent.
