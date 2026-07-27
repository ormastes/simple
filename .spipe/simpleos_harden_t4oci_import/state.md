# Lane T4-OCI — Podman "OCI at the edge" import adapter

Status: DONE (pure model). Files left in working copy (not committed).

## Files
- `src/os/services/container/oci_import.spl` (new) — edge adapter.
- `test/01_unit/os/services/container/oci_import_spec.spl` (new) — absolute-oracle spec.
- container_manager.spl / container_namespace.spl / kernel: UNCHANGED (import only).

## What it is
`oci_import(input: OciConfigInput, policy: OciPolicy) -> Result<ContainerSpec, text>`
(bare Ok/Err — cross-module Result.Ok/Err is a filed compiler bug). Takes an
already-parsed/normalized OCI config struct (NO IO — no bundle unpack, no
registry pull, no file reads) and converts it to the manager's `ContainerSpec`
after fail-CLOSED §6.3 validation. A plain `oci_import_checked(...) ->
OciImportResult{ok,error,spec}` core is also exposed so the spec never has to
match a cross-module Result.

## Six safety checks (§6.3) — each a DISTINCT error string
| # | Check | Trigger | Error string (substring asserted) |
|---|-------|---------|-----------------------------------|
| a | `..` traversal / above-root | any mount `dest` contains `..` | `oci reject: mount destination escapes container root (.. traversal / above-root)` |
| b | raw host bind mount | mtype=="bind" & src is host path (`/...`) & `!policy.allow_host_mounts` (default false) | `oci reject: raw host bind mount denied by policy (allow_host_mounts=false)` |
| c | uncontrolled device node | mtype=="device" & `!policy.allow_devices` | `oci reject: uncontrolled device node mount denied by policy (allow_devices=false)` |
| d | lifecycle hooks | `input.hooks_present` & `!policy.allow_hooks` | `oci reject: lifecycle hooks present but not authorized (allow_hooks=false)` |
| e | unpack size/count bound | `unpack_count > max_unpack_count` or `unpack_size > max_unpack_size` | `oci reject: unpack size/count exceeds policy bound` |
| f | missing digest | `policy.require_digest` & `digest.len()==0` | `oci reject: missing or empty content digest but require_digest=true` |

`oci_policy_default(ceiling)` = all permissive flags false, require_digest true,
100k-entry / 1 GiB unpack bounds. Fail-closed by construction.

## ContainerSpec mapping (success path)
- `image_digest` = input.digest
- `root` = input.root_path
- `caps` = INTERSECTION(input.caps, policy.cap_ceiling) — subset of BOTH, never
  amplified; any raw host-net token (`cap.host_net` / `cap.net_host` /
  `cap.net_host_raw`) is STRIPPED → default net isolated.
- `budget` = input.mem_budget
- `spec_is_isolated_net(spec)` helper proves no host-net cap survived.
- UID/GID: carried on the input and normalized upstream; ContainerSpec (manager
  struct, not modifiable here) has no uid/gid/net/entrypoint slot, so those
  don't round-trip into the spec — noted as a model boundary, not a gap in the
  checks.

## Spec verdict
Ran via `/tmp/t4oci/bin/t4job run test/01_unit/os/services/container/oci_import_spec.spl`:
- benign import: **2 examples, 0 failures**
- six rejects: **6 examples, 0 failures**
- policy widen (host mount admitted when allowed): **1 example, 0 failures**
- traversal-check load-bearing: **1 example, 0 failures**
- Total: **10 examples, 0 failures.**
- Fail-once proof: set `dest_escapes -> false`, cleared native_cache → the (a)
  traversal-reject test FAILED (`6 examples, 1 failure`); restored → back to
  0 failures. Check is load-bearing.
- The `self.` info hints in output come from the imported container_manager.spl
  (line 385), not this lane's code — cosmetic, non-fatal.

## Blockers / out of scope (pure model only)
- NO live OCI bundle unpack — adapter consumes a parsed struct; real tar/layer
  extraction + on-disk symlink/hardlink resolution not done.
- NO registry pull — image_ref/digest are trusted inputs; signature VERIFY not
  implemented (only digest-presence check f).
- NO QEMU / no live spawn — ContainerSpec is a model, not submitted to the
  kernel spawn broker.
- Traversal check is TEXTUAL (`..` substring) — a real unpack must also resolve
  escaping symlinks/hardlinks against the materialized root.

## Next increment
1. Real bundle read: tar-layer walk that materializes the rootfs and runs the
   symlink/hardlink escape resolution against the actual tree (not just text).
2. Signature verification (cosign-style) to strengthen check (f) from
   presence to cryptographic validity.
3. Wire `oci_import` → `sys_create` end-to-end, then `sys_monitor` / `sys_gc`
   (ref-counted COW layer reclaim) per the master plan §6.4.
