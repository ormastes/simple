# BS6 Optional-Provider Qualification Matrix

**Executable spec:** `test/03_system/runtime/provider/optional_provider_qualification_matrix_spec.spl`

## Purpose

This matrix proves that optional providers remain metadata-only until first
demand, preserve feature and typed-error behavior, execute effects once, and
remain reversible under absence, corruption, concurrency, crash, and rollback.
It also prevents binary-size work from silently removing a provider family or
supported native architecture.

## Evidence Policy

- Portable source-contract scenarios execute on every host.
- Provider-family rows consume `provider-family-parity-v1` receipts.
- Architecture rows consume `provider-matrix-v1` receipts.
- Missing native receipts are reported as pending, never PASS.
- A receipt is insufficient unless it binds target, binary hash, provider-set
  hash, feature parity, error parity, absence, corruption, concurrency, crash
  recovery, rollback, metadata-only admission, and zero hidden provider loads.
- Static source inspection does not qualify native behavior.

## Portable Scenarios

1. Admission precedes loader adaptation and effect-ticket construction.
2. Admission contains no `dlopen`, `LoadLibrary`, process execution, or hidden
   effect-ticket creation.
3. No-import hello retains the explicit zero-DSO/zero-initialization contract.
4. Missing/corrupt capability, package, ABI, and dependency authority produce
   typed fail-closed errors.
5. Admission uses atomic single-flight publication and cached rejection.
6. Dual mode names one effect owner; shadow mode remains metadata-only.

## Provider Families

The executable matrix requires independent parity receipts for:

- file and archive;
- network and web;
- crypto;
- database;
- compression and XML;
- TUI, UI, and audio;
- GPU.

Each family receipt must prove feature parity, typed-error parity, exactly one
effect execution, and rollback.

## Architecture Rows

| Target | Required status |
|---|---|
| `x86_64-unknown-linux-gnu` | Native receipt required |
| `aarch64-unknown-linux-gnu` | Native receipt required |
| `aarch64-apple-darwin-macho` | Native receipt required |
| `x86_64-apple-darwin-macho` | Native receipt required |
| `x86_64-pc-windows-msvc` | Native receipt required |

## Failure Matrix

Every architecture receipt must demonstrate:

1. feature and normalized error parity;
2. absent provider rejection without undeclared fallback;
3. corrupt artifact rejection before mapping/effects;
4. one publication under concurrent demand;
5. crash recovery without partial provider visibility;
6. explicit rollback to the retained provider generation;
7. metadata-only admission before execution authority;
8. zero hidden sibling-provider loads.

## Current Qualification

Portable admission and isolation contracts are executable. Native and
provider-family rows remain pending until their hash-bound runtime receipts are
produced. This manual does not claim those unavailable rows pass.

