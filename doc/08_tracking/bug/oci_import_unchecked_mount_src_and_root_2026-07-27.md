# BUG: oci_import accepted escaping mount sources, escaping container roots, and type-spoofed host/device mounts

- **Status:** FIXED 2026-07-27 (lane CESC)
- **Severity:** HIGH — container escape at the OCI import edge
- **Component:** `src/os/services/container/oci_import.spl`
- **Found by:** `test/01_unit/os/services/container/container_escape_suite_spec.spl`
- **Related:** master plan §6.3 (OCI safety checks), `src/verification/os_enforcement/OciImport.lean`

## Summary

The "OCI at the edge" adapter is the fail-closed validation boundary between an
untrusted bundle and the manager's capability model. Four of its §6.3 checks
were incomplete. Each defect let a hostile `config.json` produce a valid
`ContainerSpec`.

The Lean model in `OciImport.lean` proves the *specified* checks are sound; it
does not prove the Simple implementation checks the same fields. All four
defects live in that gap.

## Defects and minimal repro

Repro harness: `oci_import_checked(input, oci_policy_default(["cap.fs_read"]))`
with every permissive policy flag FALSE.

### 1. Mount SOURCE traversal unchecked

`dest_escapes()` was applied to `mnt.dest` only. The raw-host-mount check used
`is_host_path()`, which matches only ABSOLUTE paths. A RELATIVE traversal source
therefore matched neither.

```
OciMount(src: "../../../etc", dest: "/cfg", mtype: "bind")   →  ok = true   (ACCEPTED)
```

### 2. `root_path` never validated

`input.root_path` was copied verbatim into `ContainerSpec.root`, which
`container_view_create()` turns into the confinement root. `"/"` is the HOST
root and `""` is the rootless sentinel.

```
root_path: "/"          →  ok = true, spec.root = "/"        (host filesystem)
root_path: "../../.."   →  ok = true, spec.root = "../../.." (above the bundle)
root_path: ""           →  ok = true, spec.root = ""
```

### 3. Bind check keyed off the type NAME

The raw-host-mount rule fired only on `mtype == "bind"`. OCI's recursive
variant spells it `rbind`, and any unrecognised type bypassed it entirely.

```
OciMount(src: "/etc", dest: "/etc", mtype: "rbind")  →  ok = true  (ACCEPTED)
```

### 4. Device check keyed off the type NAME

Same class: the rule fired only on `mtype == "device"`.

```
OciMount(src: "/dev/mem", dest: "/dev/mem", mtype: "devtmpfs")  →  ok = true  (ACCEPTED)
```

## Fix

- new `src_escapes()` — reject any mount whose SOURCE contains `..` (no
  legitimate OCI source, bind path, volume name, or pseudo-fs token, does);
- new `root_path_invalid()` — reject `""`, `"/"`, and any `..` in `root_path`;
- the raw-host-mount rule is now TYPE-INDEPENDENT: any mount naming an absolute
  host path as its source is a raw host mount, so `rbind` and unknown future
  types are covered automatically. Pseudo filesystems name their source
  `tmpfs`/`proc`/`none` and are unaffected;
- `is_device_family()` covers `device`, `devtmpfs`, `mknod`.

Two new distinct rejection strings: `ERR_SRC_TRAVERSAL`, `ERR_ROOT`.

## Follow-up

`OciImport.lean` should be extended so the model quantifies over the mount
SOURCE and the container root, not just the destination — otherwise the same
gap can reopen without the proof noticing.
