# container_escape_suite — lane CESC state

**Roadmap row:** Phase 5 blocked row — "container escape suite + live lookup-site wiring"
**Date:** 2026-07-27
**Status:** suite half DELIVERED; live lookup-site wiring half REMAINS BLOCKED (see below)

## Deliverable

`test/01_unit/os/services/container/container_escape_suite_spec.spl` — 32
adversarial `it` blocks across 6 describe blocks. Every block is a genuine
break-out attempt against the real Simple implementation
(`container_manager.spl`, `oci_import.spl`, `container_namespace.spl`), with
absolute oracles (literal `deny` / `false` / named rejection strings) and
fail-closed expectations. No self-comparison anywhere.

## Spec verdict

`bin/simple test test/01_unit/os/services/container/container_escape_suite_spec.spl`

```
6 examples, 0 failures      escape/path
6 examples, 0 failures      escape/caps
6 examples, 0 failures      escape/namespace
5 examples, 0 failures      escape/leakage
6 examples, 0 failures      escape/storage
3 examples, 0 failures      escape/calibration
Results: 32 total, 32 passed, 0 failed
```

Log: `build/cesc_probe/suite_run.log`. Every attack is GREEN meaning the
implementation REFUSED it — no attack is green by observing a permissive
result.

The three pre-existing container specs are green with the fixes in place (run
sequentially, one spec target each — never a whole-suite run):

```
container_manager_spec      Results: 8 total, 8 passed, 0 failed
container_monitor_gc_spec   Results: 13 total, 13 passed, 0 failed
oci_import_spec             Results: 10 total, 10 passed, 0 failed
```

`oci_import_spec` staying 10/10 matters: the new fail-closed checks reject the
attacks without rejecting any legitimate import the existing spec exercises.

**A/B (JIT vs interpreter):** `build/cesc_probe/probe1.spl` +
`probe2.spl` produce byte-identical verdicts under `bin/simple run` and
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`. No JIT/interp divergence.

**Lint delta: zero.** `bin/simple lint` on the two changed sources reports the
same 2 errors (`COLL006` false positives on `out = out.push(c)`, plus a
pre-existing `method get not found on type str`) as the unmodified HEAD copies
of the same files — verified by linting `git show HEAD:` versions side by side.

## Attack coverage

| # | Attack | Verdict |
|---|--------|---------|
| 1 | `..` traversal in a resolved path | DENIED (never normalized) |
| 2 | Absolute host path outside root (`/etc/shadow`, `/`, `/proc/1/root`) | DENIED |
| 3 | Prefix confusion (`/rootfsevil` vs `/rootfs/`) | DENIED — was already correct |
| 4 | OCI mount DEST traversal | REJECTED (`escapes container root`) |
| 5 | OCI mount SOURCE traversal (`../../../etc`) | **HOLE — FIXED** |
| 6 | OCI `root_path` = `/`, `""`, `../../..` | **HOLE — FIXED** |
| 7 | OCI caps beyond the policy ceiling | Intersected away |
| 8 | Spawn request caps > granted | Never (subset proven) |
| 9 | Restart re-requesting caps beyond create-time grant | **HOLE — FIXED** |
| 10 | Restart widening root to `/` | **HOLE — FIXED** (same fix) |
| 11 | Restart NARROWING root (control — clamp is not a blanket reset) | Allowed |
| 12 | Pod member inheriting a co-member's caps | Never crosses |
| 13 | Sibling container's path | DENIED |
| 14 | Sibling container's pid, and host pid 1 / pid 0 | DENIED |
| 15 | Pod mask asking for NS_MOUNT + NS_PID | net/ipc share; mount/pid do NOT widen |
| 16 | Rootless default view resolving anything | DENIES all paths and all pids |
| 17 | STOPPED container resolving anything | DENIED, pouch empty, endpoints 0 |
| 18 | EXITED container after a pod wired it | DENIED, pod net handle revoked |
| 19 | Host-net cap tokens, even when the ceiling lists them | Unconditionally stripped |
| 20 | Device mount `device` / `devtmpfs` / `mknod` | REJECTED — `devtmpfs` was a **HOLE — FIXED** |
| 21 | Raw host bind as `bind` / `rbind` / unknown type | REJECTED — `rbind` was a **HOLE — FIXED** |
| 22 | Lifecycle hook injection | REJECTED |
| 23 | Unsigned image + unpack bomb (size and count) | REJECTED |
| 24 | Two containers off the same base sharing a COW writable layer | **HOLE — FIXED** |
| 25 | Cross-container COW write bleed | Isolated |
| 26 | Write past own COW quota | Refused, nothing written |
| 27 | Reaching a removed container's layers via refcount | Unreachable, refcount 0 |
| 28 | GC reclaiming a LIVE container's layer | Never |
| 29 | Manager restart leaving brokered grants alive | All torn down |

## Real holes found and fixed

Five genuine defects, all found by writing the attack first. Filed with minimal
repros:

- `doc/08_tracking/bug/oci_import_unchecked_mount_src_and_root_2026-07-27.md`
  — four defects in one file: unchecked mount SOURCE traversal, unvalidated
  `root_path` (`/` and `""` accepted as the container root), and the raw-host
  and device checks keyed off the mount TYPE NAME so `rbind` / `devtmpfs`
  bypassed them. Fixed: `src_escapes()`, `root_path_invalid()`, a
  type-independent absolute-host-source rule, `is_device_family()`.
- `doc/08_tracking/bug/container_restart_no_cap_ceiling_2026-07-27.md`
  — `sys_restart` had NO ceiling: the §21 teardown empties `granted_caps`, so
  nothing bounded the re-acquisition and a crash-loop was a privilege-escalation
  primitive (`cap.sys_admin` + root `/`). Fixed with frozen `ceiling_caps` /
  `ceiling_roots` columns + `attenuate_caps()` / `clamp_root()`.
- `doc/08_tracking/bug/container_cow_layer_id_aliased_across_containers_2026-07-27.md`
  — the COW writable layer id was `image_digest + ":cow"`, identical for every
  container off the same content-addressed base. Fixed by appending the
  container id.

## Deliberate-red calibration

Three calibration cases (describe block 6) drive the production code through
its own defect-injection knobs and show the SAME oracles observe a breach:

1. `sys_create(..., seed_global_root: true)` — the breached container returns
   `path_decision("/etc/shadow") == "allow"`, i.e. section 1's `deny` oracle
   goes RED against a breached build. The correctly-built container in the same
   world returns `deny`, so the two differ by the defect alone.
2. `oci_import_checked_ex(attack, policy, check_traversal: false)` — the same
   hostile config that production REJECTS imports cleanly (`ok == true`,
   `error == ""`), so section 1's `ok == false` oracle is load-bearing.
3. `container_view_create("/", pids)` — the primitive `svc_world_invariant`
   consults reports `allows_path("/etc/shadow") == true`, proving the §21
   detector is not a constant-true.

Additionally, three of the five holes above were observed RED before the fix and
GREEN after (probe transcripts in `build/cesc_probe/`): mount-source traversal
`ok=true → ok=false`, `root_path="/"` `ok=true → ok=false`, restart escalation
`allows_path("/etc/shadow") true → false`, COW ids `sha256:same:cow` twice →
`:cow:1` / `:cow:2`. That is the strongest form of the calibration: the suite is
known to fail against the code as it actually shipped this morning.

## What this suite does NOT cover — stated plainly

It exercises **Simple-level enforcement only**: the pure model of the manager,
the OCI edge adapter, and the kernel namespace primitive.

- **No live kernel wiring.** No real VFS lookup site consults
  `container_view_allows_path`; no syscall path is exercised; nothing runs in a
  QEMU guest or on a board. The "live lookup-site wiring" half of the Phase 5
  row is UNCHANGED and still BLOCKED.
- **No dynamic path resolution.** `..` is refused textually rather than
  normalized, and symlinks do not exist in this model. A real VFS that resolves
  symlinks needs its own escape suite at the lookup site — a symlink whose
  TARGET escapes cannot be modelled here at all.
- **Enforcement vs. orchestration.** `container_manager` is orchestration by
  design; the security boundary is the kernel view. This suite proves the
  handles the manager builds are correct, not that the kernel honours them.
- **Storage isolation is a NAME-level proof.** The COW fix guarantees distinct
  writable-layer IDs; whether a real overlay backend mounts them separately is
  untested.
- **Not covered by the Lean proofs either.** `ContainerIsolation.lean` /
  `OciImport.lean` model the SPEC; all five holes lived in the gap between the
  model and the Simple implementation. Follow-ups noted in the bug docs:
  quantify the OCI model over mount SOURCE and container root, and add a
  storage-isolation theorem.

## Landmine hit during this lane (for the coordinator)

`container_monitor_gc_spec.spl` was silently REVERTED on disk between the edit
and the test run — a parallel session's sync restored the pre-edit copy, and
the run failed 2/13 asserting the OLD cow-layer ids while the source already
emitted the new ones. Symptom to recognise: a failure whose EXPECTED value is
the value you just replaced. Re-applied and re-verified 13/13. Anyone landing
this change should re-`grep` the two `cow:1` assertions after any rebase or
sync — the source fix and the spec assertion must land together or the spec
goes red.

## Files touched

- `test/01_unit/os/services/container/container_escape_suite_spec.spl` (new)
- `test/01_unit/os/services/container/container_monitor_gc_spec.spl` (two COW
  layer-id assertions updated for the per-container id — the fix changed the
  value they assert; neither assertion was weakened)
- `src/os/services/container/oci_import.spl` (4 hole fixes)
- `src/os/services/container/container_manager.spl` (2 hole fixes)
- `doc/08_tracking/bug/*_2026-07-27.md` (3 bug docs)
