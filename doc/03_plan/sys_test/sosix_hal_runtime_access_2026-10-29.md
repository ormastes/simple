# SOSIX/HAL runtime accessibility acceptance — 2026-10-29

Owner split: Astra plans and reviews; Luna writes and executes the Simple SSpec;
the integration owner lands only reviewed, source-matched evidence. No shared P2
binary is rebuilt or replaced by this lane.

## Evidence boundaries

Every receipt records source commit, runtime path and SHA-256, OS/architecture,
command, mode, exit code, executed/passed/failed/skipped example counts, and log.
Interpreter behavior, compiled Simple behavior, and C owner selfchecks are
different evidence rows. A zero-example exit, import-only success, source scan,
mocked value allocator, or skipped example never proves native Simple access.
Expected unavailable responses prove refusal only, not a working process provider.

## Immediate Mac acceptance

`test/03_system/runtime/sosix_host_runtime_access_spec.spl` calls exported SOSIX
leaves rather than declaring application-local `rt_*` externs. Its five examples:

1. The real platform owner reports `macos` and the process owner returns PID > 0.
2. `/bin/sh` exists and a unique nonexistent path does not.
3. `PATH` is present/nonempty and a unique absent environment key remains nil.
4. Two monotonic samples advance across a bounded SOSIX sleep; realtime
   nanoseconds exceed 10^18. The first monotonic sample may be zero because a
   provider can use a process-local origin. Provider errors fail explicitly;
   clock domains are never substituted and a constant-zero provider must fail.
5. V1 provider selection reaches the capability owner and reports `Unsupported`
   on Mac. The runtime currently advertises V3-backed observation only on Linux
   when its pidfd/identity probe succeeds.

The Mac test must be explicitly scoped to Mac; an `if` branch with no assertions
on another host is forbidden. Execute it once per mode with a bounded command.
Check the exact five-example result before reporting a pass. A native compile,
link, or runtime failure stays blocked with its first actionable diagnostic.

## Platform/API matrix

| API boundary | Mac | Linux | Windows | FreeBSD / SimpleOS | Required evidence |
|---|---|---|---|---|---|
| Host identity, file predicate, env lookup, clocks | Immediate Simple spec above | Same semantic assertions with Linux fixture | Native Windows path/env fixture | Native target fixture | Separate interpreter and compiled Simple receipts |
| SOSIX V1 unsupported refusal / malformed receipt | Existing two-example boundary spec | Same deterministic refusal contract | Same contract | Same contract | Portable Simple execution; no positive-provider claim |
| SOSIX V1 selected provider | Must report Unsupported | Available only after actual pidfd/identity capability admission | Must report Unsupported in current source | Must report Unsupported in current source | Live capability query; no OS-name inference |
| V4 capabilities | Unavailable, zero limits/caps, positive error | Receipt-dependent; validate exact profile before positive claim | Receipt-dependent, host validation required | Receipt-dependent, host validation required | Native Simple capability spec; interpreter skips authority examples |
| V4 cwd pin | Pin root, 32-byte digest, close, post-close refusal | Host-specific owner acceptance | Host-specific owner acceptance | Host-specific owner acceptance | Actual native Simple lifecycle plus independent C owner checks |
| Mac cooperative snapshot | Explicit trusted-snapshot-group profile only | Not applicable | Not applicable | Not applicable | Existing runner/API C gates; compiled Simple route remains separate |
| Strict V4 launch / descendant containment | Unavailable; no fallback to cooperative snapshot | Own profile-specific adversarial host suite | Own profile-specific adversarial host suite | Own profile-specific adversarial host suite | Refuse before spawn or prove exact profile, bounds, deadlines, retirement and ACK |

Foreign-host rows are **not executed by this Mac lane**, not passed. A shared
portable API or available source implementation is not cross-platform evidence.

## Exact gates and review requirements

The V1 boundary and V4 HAL specs below belong to the separate
`work/sosix-hal-foundation-tests-20261029` integration lane. Their original
commit was `49a07dbff3b`; use that lane's final merged commit before executing
these references. They are not supplied by the host-access smoke spec.

- `test/02_integration/lib/sosix/process_observation_boundary_v1_spec.spl`:
  unsupported request must not spawn or return a PID; empty/nonempty unknown
  receipt vectors remain Missing/Malformed.
- `test/02_integration/lib/io/process_observation_hal_capabilities_v4_spec.spl`:
  one portable deadline-overflow example; two native examples on Mac. Native
  capabilities must not accidentally advertise strict Mac availability. Cwd
  ownership must be invalid after close.
- `scripts/check/check-sosix-darwin-process.shs` and
  `scripts/check/check-sosix-v4-darwin-foundation.shs`: C component evidence only;
  foreign host exit 77 is a skip. They do not qualify the deployed Simple facade.

Review blocks acceptance for fabricated constants, empty host branches,
unconditional successful stubs, failure converted to skip, incorrect example
counts, unrecorded runtime identity, or claiming strict support from cooperative
or C-only evidence. Review the exact final diff before integration.
