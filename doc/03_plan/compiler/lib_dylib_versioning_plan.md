# Library and Dynamic-Library Versioning Plan

Status: active, 2026-10-27. Lane: lib-versioning. Base branch: `release/1.0.0`.
Design: `doc/05_design/compiler/lib_dylib_versioning.md`.

## Scope

This plan covers every artifact that the sibling lanes turn into a library:

| Kind | Owner lane | Source of truth |
|---|---|---|
| Static stdlib archive | backend-dylib | `config/build/stdlib_static.sdn` |
| Backend plugin dylib (v1 ABI) | backend-dylib | `src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h` |
| CPU-tier dylib | SIMD | `config/build/cpu_tiers.sdn` |

This lane owns the version identity, the compatibility rules and the admission
logic, in `src/compiler/80.driver/libver/`, plus its sub-config
`config/build/lib_versioning.sdn`. The owner lanes wire the call sites in their
own files. This lane never edits those files.

## Version identity (`LibIdentity`)

| Field | Meaning |
|---|---|
| `name` | Logical library name, for example `simple_std` or `backend_llvm` |
| `semver` | `MAJOR.MINOR.PATCH[-pre]` |
| `abi_major`, `abi_minor` | Binary ABI. For plugins, `abi_major` equals `SIMPLE_BACKEND_PLUGIN_ABI_V1`. |
| `iface_digest` | `interface_digest_of` from `action_key.spl` (`simple/interface/v1`) |
| `iface_parts` | Optional sorted list of interface items, used for the subset check |
| `producer` | Compiler fingerprint of the producing compiler |
| `triple` | LLVM target triple |
| `cpu_tier` | LLVM level name (`x86-64-v1`..`v4`, `armv8-a`.., `rv64gc`..). `generic` means no tier. |
| `sha256` | sha256 of the artifact bytes |

## Compatibility rules

A consumer admits an artifact only when all of the following hold:

- the name matches;
- `abi_major` is equal, and `abi_minor` is at most what the consumer supports;
- `abi_major` falls within the support window (current major, or N-1 while it is marked deprecated);
- the triple is equal;
- the tier base rank is at most the host's base rank on the same arch, and every artifact feature is in the host's feature set;
- the digest is equal, or the artifact's `iface_parts` is a superset of the parts the consumer needs;
- the artifact's sha256 equals the sidecar's `sha256`.

Any other case is refused, and fails closed with a `LibRefusal` enum value:
`NameMismatch`, `AbiMajorMismatch`, `AbiMinorTooNew`, `AbiOutOfWindow`,
`TripleMismatch`, `TierTooHigh`, `TierUnknown`, `DigestMismatch`,
`HashMismatch`, `ProducerMismatch` (only when the host pins a producer), `SidecarMissing`, `SidecarMalformed`.

## Naming and side-by-side install

- Static archive: `libsimple_std-<semver>-<triple>-<tier>.a` (`.lib` on Windows gnu also uses `.a`).
- Backend plugin: `backend_<name>-<triple>-v<abi>.<dll|so|dylib>`. This form was agreed with the backend-dylib lead: providers are one per triple, and host-agnostic providers use their emit triple.
- CPU-tier dylib: `lib<name>-<semver>-<triple>-<tier>.<ext>`.
- Sidecar: `<artifact file>.lib.sdn`, holding the `LibIdentity` fields. Its `sha256` field covers the artifact.
- Install root: `lib/simple/<triple>/`. Because the version and tier are part of the file name, several versions can be installed side by side.

## Phasing

- **PR-1**: the plan and design docs, and the `lib_versioning.sdn` sub-config (AC-1, AC-11).
- **PR-2**: `libver` core, covering identity, naming, sidecar emit and parse, and the admission check, with specs (AC-2..AC-8).
- **PR-3**: the cache-key and sub-config carrier, and the release-publish manifest helper (AC-9, AC-10).
- **Hand-off**: one-line hooks to the backend-dylib and SIMD leads (AC-12, which those owners track).

## Acceptance criteria

- **AC-1**: `config/build/lib_versioning.sdn` exists. It declares the naming patterns, the sidecar suffix, the ABI support window (`abi_window: 1`) and the install root. Check: the spec parses it, and it fails if a key is missing.
- **AC-2**: `LibIdentity` round-trips through the sidecar SDN, so emit then parse gives back the same fields. A missing field gives `SidecarMalformed`. Check: `test/unit/compiler/driver/libver/libver_sidecar_spec.spl`.
- **AC-3**: The file name builders produce the three naming forms exactly, and parsing a name recovers name, semver or ABI, triple and tier. Check: `libver_naming_spec.spl`.
- **AC-4**: ABI rules. An equal major is admitted. A different major gives `AbiMajorMismatch`, unless the artifact's major is N-1 inside the window. A minor newer than the consumer's gives `AbiMinorTooNew`. Check: `libver_admit_spec.spl`.
- **AC-5**: Tier rules, which form a partial order as agreed with the SIMD lead. A tier is `<base level>[+feat...]`. It is admitted only when all of the following hold: it is the same arch, `base_rank(artifact)` is at most `base_rank(host)` using the `levels` order in `cpu_tiers.sdn`, and every feature of the artifact is in the host's feature set. A higher base, or a missing feature, gives `TierTooHigh`. An unknown base gives `TierUnknown`. `x86-64-v1` is an alias of `x86-64`. Check: `libver_admit_spec.spl`.
- **AC-6**: Digest rules. An equal digest is admitted. A superset of `iface_parts` is admitted. Anything else gives `DigestMismatch`. The digest is computed with `interface_digest_of`. Check: `libver_admit_spec.spl`.
- **AC-7**: Hash, triple and name rules. A sha256 mismatch gives `HashMismatch`, a triple mismatch gives `TripleMismatch`, and a name mismatch gives `NameMismatch`. Check: `libver_admit_spec.spl`.
- **AC-8**: The refusal reason is an enum (`LibRefusal`), with no `Any` and no bare strings in the API, and every refusal reports its name through `.name()`. Check: a spec, plus a grep gate showing no `Any` in `src/compiler/80.driver/libver/`.
- **AC-9**: `libver_cache_component(id)` gives a canonical text that contains semver, ABI, digest, producer, triple and tier. Changing any one field changes it. Check: `libver_cache_spec.spl`.
- **AC-10**: `libver_publish_manifest(ids)` emits a deterministic, sorted SDN release manifest listing each artifact's file name and sha256, to be consumed by the rc pipeline. Check: `libver_publish_spec.spl`.
- **AC-11**: The design doc records the upgrade and deprecation policy: N-1 ABI major support for one minor release cycle, deprecation marked in `lib_versioning.sdn`, and refusal after the window. Check: the doc exists and has a "Deprecation" section.
- **AC-12a** (static, lands first): `libver_link_check(archive_file_name, sidecar_text, host)` refuses an archive whose file name does not parse or disagrees with its sidecar (`NameMismatch`), then applies AC-4..AC-7. Check: `libver_link_check_spec.spl`. The stdlib link step calling it is wired by the backend-dylib lane.
- **AC-12b** (dylib, second): the dynamic loader calls `libver_admit` before resolving `simple_backend_plugin_v1`; the GPU runtime slot reuses the same sidecar. Owner: backend-dylib lane; tracked in its plan, verified here by grep for the call site once landed.

### Per-host ACs (names, sidecar, checks on every supported OS)

`libver_platform_names(triple, name, abi_major, abi_minor)` gives each OS's loader identity. A host that cannot be reached for a real run is recorded as a BLOCKED row, never as PASS.

- **AC-13 Linux**: ext `so`; soname `lib<name>.so.<abi_major>`. Spec: `libver_platform_spec.spl`. Real-host gate: run the libver specs on a Linux host.
- **AC-14 Windows** (llvm-mingw UCRT `x86_64-pc-windows-gnu`): ext `dll`; DLL name `<name>-v<abi_major>.dll`, no soname. Spec plus real-host run on Windows.
- **AC-15 macOS**: ext `dylib`; install_name `@rpath/lib<name>.<abi_major>.dylib`; compatibility_version `<major>.<minor>.0`. Spec plus real-host run.
- **AC-16 FreeBSD**: ext `so`; soname as on Linux. Spec plus a run in the FreeBSD QEMU lane (`scripts/check/check-freebsd-bootstrap-qemu.shs`).
- **AC-17 SimpleOS**: ext `so`; soname as on Linux. Spec plus an in-guest run; the board-runnable rule applies.

## Ordering

Static first: AC-1..AC-3, AC-9..AC-11 and AC-12a land first, followed by a Fable review. Dylib admission (AC-12b) comes after. The per-host ACs AC-13..AC-17 apply to both.
