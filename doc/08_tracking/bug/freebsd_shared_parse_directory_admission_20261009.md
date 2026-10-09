# FreeBSD directory admission disables frontend cache reuse

Status: OPEN. Area: compiler frontend cache / SOSIX directory capability.
Observed source: release `11f9047d82565507e273d97ec3285c01f497f2d5`; runtime capsule fix `9181640c4c010141d9e3fd5541a3cc976b42ff7c` preserves this capability limitation.

## Trigger and behavior

On FreeBSD, configure a nonempty `SIMPLE_SHARED_PARSE_CAS_ROOT` and a private frontend cache directory. `frontend_cache_root_admission_v1` requires `sosix_directory_pair_check_v1(...) == 0`. The existing runtime directory owner supports Linux and Windows; its other-platform branch returns `-ENOTSUP` for root opening. Valid FreeBSD directory roots therefore fail admission.

`frontend_parse_cache_enabled()` then returns false, disabling private frontend cache reuse. `_shared_parse_key_for_v1` returns an empty key, preventing shared parse cache lookup/publication. An empty shared root bypasses admission. `SIMPLE_BOOTSTRAP=1` independently disables shared parse keys. These callers do not directly abort compilation.

This records a missing cache capability, not a measured performance regression: no before/after timing benchmark has been run.

## Evidence

- `src/runtime/runtime_sosix_directory_roots_v1.h`: non-Linux/non-Windows `rt_sdr_root_open_v1` returns `-ENOTSUP`.
- `src/compiler/10.frontend/frontend_cache_root_admission_v1.spl:15`: shared/private root admission.
- `src/compiler/10.frontend/frontend_parse_cache.spl:89`: cache enabled decision uses directory admission.
- `src/compiler/10.frontend/frontend_shared_parse_cas_v1.spl:196`: shared key selection returns empty after admission failure.
- Native FreeBSD proof `/root/freebsd-bootstrap-capsule-proof-20261009/abi.c` asserts `rt_sdr_check_v1("/tmp", "/var/tmp") == -ENOTSUP`; three ABI/capability assertions passed, guard exit 0.

## Required correction and acceptance

Implement native FreeBSD descriptor-owned directory admission with real no-follow ancestry, disjointness, identity and replacement checks. Preserve rejection semantics and the runtime array owner. Do not bypass admission or return fabricated success.

Verify valid disjoint roots succeed; identical/ancestor roots, symlink ancestry and replaced roots reject. Verify private/shared frontend caches actually reuse admitted entries on FreeBSD; then measure cold/warm compiler behavior before making performance claims. The symbol-linking fix alone does not satisfy these capability criteria.
