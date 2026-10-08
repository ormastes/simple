# Dynamic provider policy before loader side effects

`provider_admit_dynamic_v1` previously opened an artifact before applying the
request's capability, host ABI, and interface policy. A refused shared object
could therefore run its native constructor. The loader now applies the shared
pure request-policy helper before `dynlib_open`; disallowed paths are rejected
before file existence/read/hash calls. The existing post-open digest reread
and `DIGEST_UNSTABLE` refusal remain in place.

The tracked regression consists of:

- `src/os/smf/provider_loader.spl`: shared policy decision and non-callable
  preflight refusal result.
- `test/01_unit/os/smf/provider_loader_policy_spec.spl`: policy precedence
  checks for path, missing artifact, digest, capability, host ABI, and
  interface major/minor.
- `test/fixtures/os/smf/provider_preopen_constructor.c` and
  `provider_loader_preopen_main.spl`: a real constructor-marker DSO and a
  standalone one-case-per-process Simple entrypoint. The positive control
  resolves the canonical two-address query symbol, verifies process-callable
  admission and constructor execution, then closes the session. It returns a
  well-formed `SIMPLE_PROVIDER_INTERFACE_UNKNOWN` query result if invoked.
- `scripts/check/test-provider-loader-preopen-side-effect.shs`: creates a fresh
  attempt directory, compiles six separately marked DSOs, and runs five denial
  cases plus the accepted control in separate processes. Every C DSO compile
  and case process is supervised with a 1 GiB RSS cap and 60-second timeout; the
  runner requires complete, successful, quiescent watchdog receipts and exact
  per-case output markers. Attempt artifacts and failures are retained.

The Simple entrypoint must first be built once with `native-build`; set
`APP_BIN` to that executable when running the side-effect script. This source
change has **not** been compiled or executed yet. The constructor-marker
matrix, unit spec, native build, watchdog receipts, and end-to-end admission
behavior remain unverified.

The pre-open ordering prevents policy-refused artifacts from being opened.
It does not close the separate time-of-check/time-of-use gap between the
pre-open digest read and the platform loader opening the path; the existing
post-open digest reread remains a detection check, not immutable-handle proof.
