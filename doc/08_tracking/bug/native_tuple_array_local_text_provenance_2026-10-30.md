# Implicit text locals from tuple-array elements lose native text representation

- **ID:** native_tuple_array_local_text_provenance_2026-10-30
- **Date:** 2026-10-30
- **Status:** OPEN (P2)
- **Lane:** Native Cranelift build using admitted Stage 2 producer
- **Owner:** Compiler/type-provenance investigation

## Symptom

With `build_query_string(params: [(text, text)])`, implicit locals extracted
from `params[i]` can lose their textual representation on the admitted native
producer. In the URL fixture, the fields had expected scalar lengths but
concatenation produced decimal pointer-like names. This is not evidence that
all tuple projections or all producers are broken.

## Evidence

- Producer: admitted Stage 2 `simple`, compiler SHA
  `9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd`.
- Runtime capsule matched that compiler SHA.
- Source was frozen in private diagnostic worktree
  `/home/yoon/dev/simple-url-query-contract-diagnostic-20261030`.
- The implicit local diagnostic source had SHA-256
  `1c85d09575b8a2c715a76dc57ef94aa39f5f067ba4e0b1abf7841a8c05dbfa21`;
  the explicit-local diagnostic source had SHA-256
  `ca1704201efdb63023ee8f1daa9f7550a6e31ebcd70e26ff72c57175df9a0792`.
  Both temporary fixture variants used SHA-256
  `214f729b0d49f5ea3e5f432824ab79cc35f2651895b6db97bb9fa38b0b9c56e9`.
  The current production source with the workaround and join correction is
  SHA-256 `56626fd50fecc434fa9bdea4b5cfc49072fa5dae156ce8205d36c215c81c36ad`;
  the unchanged contract fixture is SHA-256
  `0fe3089a5b2efffaf3b396344b40bdd1ff0a8bec0f9042f08fc12820926ff97d`.
- With the array receiver corrected to `parts.join("&")`, but without local
  type annotations, direct ASCII and UTF-8 encoders were correct. The builder
  reported `name_len=1` and `value_len=11`, but built a name such as
  `198946527114577`; the final expected-string assertion failed with `-7`.
- An isolated diagnostic variant added explicit local types:
  `param: (text, text)`, `name: text`, and `value: text`. It built
  `a=hello%20world&emoji=caf%C3%A9`, passed ordered duplicate-key roundtrip,
  and printed `URL_QUERY_CONTRACT_PASS|checks=8`.
- Diagnostic captures and source hashes remain under the named worktree's
  `build/url-query-contract-debug` and `build/url-query-contract-explicit`
  directories. Temporary diagnostic prints are not part of the production
  patch. The committed fixture passes with the workaround; removing the
  explicit local annotations is what reproduces the failure on this producer.

## Scope and follow-up

Keep explicit local annotations at this call boundary until the producer's
tuple-field type provenance is understood. The evidence does not identify the
compiler phase that loses the text type, and does not close a compiler bug.
Do not weaken `[(text, text)]`, erase the public type, or add unsafe casts.
Add a compiler-level regression and remove this workaround only after a
producer-bound fix passes the native fixture.
