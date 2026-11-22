# Windows Docker specs still expect pre-V6 network and version refusals

- **Status:** FIXED (2026-11-22)
- **Component:** `src/lib/nogc_async_mut/container/providers/windows/docker_contract_v1.spl:170-172`,
  `src/lib/nogc_async_mut/container/providers/windows/docker_codec_v1.spl:76`
- **Found:** 2026-11-22, Phase 1 (seed `ac2e90625c2a`) run of the Windows provider specs on a
  Windows 11 host, while qualifying the provider against a live Windows engine.

## Symptom

| spec | example | expected | actual |
|---|---|---|---|
| `test/03_system/app/orchestrator/feature/windows_docker_process_contract_spec.spl:83` | rejects unsupported networking | `docker-network-none-required` | `docker-network-policy-required` |
| `test/03_system/app/orchestrator/feature/windows_docker_process_contract_spec.spl:191` | rejects wrong schema | contains `version:version` | `docker-request-record-invalid:missing_field:.environment` |
| `test/01_unit/lib/nogc_async_mut/container/shared/provider_conformance_v1_spec.spl:285` | Windows hard-requires network none | `docker-network-none-required` | `docker-network-policy-required` |

## Cause

`4cd3ba3d325` (feat(container): bind Windows discovery to approved NAT networks) made a
selected network legal when the policy names an administrator-approved network, so a
non-`none` network without one now refuses with `docker-network-policy-required`. The
codec also admits request versions 1..6, so `version: 5` is a valid V5 record that then
misses `environment`. The three expectations were written before that change and never
updated; the source behaviour is the intended V6 contract.

## Fix

Specs only, same strength: the network examples assert the V6 refusal reason, and the
schema example uses `version: 7`, the first unsupported version, which still must be
refused at `version:version`.

## Verification

Phase 1, `test <spec> --mode=interpreter --assert-ran`:
`windows_docker_process_contract_spec` 21/21 (was 19/21), `provider_conformance_v1_spec`
11/11 (was 10/11).
