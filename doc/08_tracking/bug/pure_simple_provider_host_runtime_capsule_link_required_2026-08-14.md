# Pure Simple provider host proof needs an admitted runtime capsule link

## Candidate repair 2026-11-03

The capsule producer now records `provider_host_link_contract`, ordered
`provider_host_link_libraries`, and `provider_host_export_policy` inside the
existing immutable manifest. `check-cli-provider-v1-host.shs --pure-capsule`
selects the new Linux integration gate. It requires an independently pinned
capsule manifest and a caller-admitted compiler with its binary digest, reuses
the complete capsule archive/object provenance validator, compiles the production
`src/app/provider_cli/native_provider_v1.spl` entry to an archive, and constructs
the provider DSO locally. No caller-supplied host DSO is an admission input.

The gate exports only the provider's undefined symbols owned by that runtime
archive. Missing named runtime owners fail before host linking; other missing
dependencies fail the strict host link or `RTLD_NOW` load. The two provider ABI
exports are selected explicitly and checked exactly. The host selfcheck checks
the Pure Simple provider's `aaaa...` ABI identity and actual command output.
The production loader and its authority checks are unchanged.

Invocation on an independently qualified Linux host:

```sh
SIMPLE_PROVIDER_RUNTIME_CAPSULE=/absolute/admitted/core-c-bootstrap \
SIMPLE_PROVIDER_RUNTIME_MANIFEST_SHA256=<independently-admitted-manifest-sha256> \
SIMPLE_ADMITTED_RUNTIME=/absolute/qualified/self-hosted/simple \
SIMPLE_ADMITTED_RUNTIME_SHA256=<qualified-compiler-binary-sha256> \
sh scripts/check/check-cli-provider-v1-host.shs --pure-capsule
```

Windows contract fixtures exercise missing capsule, missing pin, wrong pin,
correctly pinned synthetic contract, unsupported dependency, and tampered
archive rejection. The positive fixture deliberately reports `execution=unrun`;
it is admission parser/provenance evidence only. Actual Linux capsule production,
Pure Simple provider compilation and host execution remain **TEST_BLOCKED /
UNRUN** in this Windows session because no qualified self-hosted full CLI is
available. This candidate does not close the bug or certify Linux execution.

## Triage 2026-09-13
OPEN, out of scope for this lane: needs an admitted runtime-capsule link
manifest and a provider-integration gate rework in the bootstrap linker path,
not a src/lib fix. Left OPEN.


Status: open.

The admitted Stage 2 compiler produced a 37 KB Pure Simple provider archive
and a host shared object with the exact two provider ABI symbols. Loading and
executing that provider requires the host process to export the runtime
services used by its codec closure.

Adding `--export-dynamic` to a selfcheck linked from monolithic
`runtime_native.c` is unsound: it defeats section garbage collection and pulls
unresolved runtime owners such as `spl_strdup`, `spl_panic`, process services,
and SIMD probes into the link.

Required fix: the provider integration gate must link the admitted, complete
runtime capsule plus its recorded dependency/link manifest, then export only
the provider-required runtime surface. It must not guess dependency archives
or weaken unresolved-symbol checks. Until that owner contract exists, the
verified evidence is archive production and exact symbol export, not full
Pure-Simple provider execution.
