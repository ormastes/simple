# SFFI v2 Hardening — Feature Requirements

**Status:** Selected and final for P0/P1  
**Research:** `doc/01_research/platform/sffi_v2_hardening_2026-08-21.md`  
**Selection:** User-selected recommended SFFI v2 architecture, 2026-08-21

## P0 — Fail closed

- **REQ-SFFI-V2-001:** The runtime shall distinguish unit fallthrough,
  explicit `Option.None`, and missing return; none is represented by another.
- **REQ-SFFI-V2-002:** A non-optional function that falls through shall fail
  with stable diagnostic `E-SFFI-016` before a caller receives a value.
- **REQ-SFFI-V2-003:** Hardened and critical profiles shall require explicit
  optional absence; accidental optional fallthrough shall fail.
- **REQ-SFFI-V2-004:** Every explicit and tail return shall be validated against
  the declared return contract at the function boundary.
- **REQ-SFFI-V2-005:** A missing or unknown foreign symbol shall be a typed,
  fatal SFFI error, never a value or successful/skipped verdict.
- **REQ-SFFI-V2-006:** Unsupported argument or result conversion shall fail;
  it shall never become nil, zero, false, empty data, or a dummy handle.
- **REQ-SFFI-V2-007:** A null function pointer shall fail before invocation.
- **REQ-SFFI-V2-008:** Hardened and critical execution shall not use the generic
  all-`i64` transmute dispatcher.
- **REQ-SFFI-V2-009:** Native, freestanding, and SimpleOS links shall not create
  weak or strong fabricated definitions for unresolved required externs.
- **REQ-SFFI-V2-010:** Signing, verification, and entropy bridge failure shall
  use typed error semantics, not empty bytes/text or zero.
- **REQ-SFFI-V2-011:** Provider-missing, unsupported, unexecuted, or skipped
  SFFI scenarios shall not satisfy a release/critical test gate.
- **REQ-SFFI-V2-012:** Interpreter, JIT, native/AOT, sealed dynload, and
  SimpleOS shall produce the same success value category or canonical error
  category for the same contract fixture.

## P1 — Canonical contracts and lift wrappers

- **REQ-SFFI-V2-101:** The compiler shall own one versioned
  `SffiFunctionContractV2` model and stable contract identifier.
- **REQ-SFFI-V2-102:** Each raw binding shall declare ABI, provider, symbol,
  target constraints, parameters, and return representation.
- **REQ-SFFI-V2-103:** Each non-unit raw binding shall use exactly one total
  return family: infallible value, nullable value, status-only, status/out,
  sentinel value, or tagged result.
- **REQ-SFFI-V2-104:** Every raw foreign call shall carry
  `UnsafeCapability.Ffi`; generated safe wrappers may contain it only locally.
- **REQ-SFFI-V2-105:** An unvalidated `ForeignRaw<T>` or equivalent HIR state
  shall not be dereferenced, exported, stored safely, or returned as safe `T`.
- **REQ-SFFI-V2-106:** Nullability/error semantics shall map to `T`,
  `Option<T>`, `Result<T,SffiError>`, or `Result<Option<T>,SffiError>` exactly.
- **REQ-SFFI-V2-107:** Pointer/resource contracts shall declare ownership,
  allocator domain, borrow scope, and required retain/release/destructor rules.
- **REQ-SFFI-V2-108:** Pointer/length/capacity, bounds, discriminant, sentinel,
  and encoding relations shall be executable validation rules.
- **REQ-SFFI-V2-109:** Unwinding across the default SFFI ABI shall be forbidden;
  provider shims translate exceptions/panics to contract errors or policy exits.
- **REQ-SFFI-V2-110:** Canonical function and registry hashes shall be
  deterministic, domain-separated, length-framed, and sensitive to every ABI
  and ownership field.
- **REQ-SFFI-V2-111:** One contract shall generate the raw declaration,
  validation/lift wrapper, provider registry material, and documentation.
- **REQ-SFFI-V2-112:** The same compiler-owned registry shall drive the
  interpreter, JIT, native/AOT, dynloader, generator, and conformance evidence.

## Later phases

P2 lexical enforcement, P3 typed provider admission, P4 cryptographic evidence,
P5 provider migration, and P6 full conformance/performance are planned. Their
presence in architecture does not claim implementation or verification.

