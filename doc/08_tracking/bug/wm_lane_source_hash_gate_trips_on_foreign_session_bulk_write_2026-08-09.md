# WM evidence lane: source-hash gate trips on a foreign session's bulk `src/lib` write

## Status

Open blocker on `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
Reproduced 2026-08-09 with a named, timestamped cause. This is the gate that
makes the SimpleOS WM lane unrunnable on a shared working tree.

## Symptom

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=wm-simple-web-build-source-changed
simpleos_wm_fullscreen_kernel_build_status=source-changed-cache-preserved
```

The run aborts **before QEMU boots**, so it produces no `serial.log`, no
screendumps, and no receipts. Every rung is lost, regardless of WM correctness.

## Mechanism

`kernel_source_manifest` (around line 252) hashes the kernel's input set —
all of `src/os`, all of `src/lib`, `build/os/generated`, and the x86_64 example
dir — **before and after** the ~151s kernel build, and refuses the kernel if
the two manifests differ. The manifest is 9,469 entries.

The existing comment at lines 236-251 already documents one instance of this
(a concurrent aarch64 lane rewriting `limine_boot_aarch64.spl` every ~90s) and
prunes foreign-architecture paths to fix it, closing with "Anything else that
churns mid-build -- including any src/lib edit -- still refuses ... Do not widen
this."

That prune is architecture-shaped, so it does not cover the case actually
observed here: a **concurrent session performing a bulk VCS write** (rebase,
snapshot, restore) that rewrites arbitrary arch-neutral `src/lib` files at once.

## Evidence (2026-08-09)

The lane aborted at ~04:06. Diffing the retained post-build manifest
`build/simpleos_wm_fullscreen_evidence/kernel-source-manifest.e0JYHX` against a
recomputation of the same 9,469 paths showed 11 differing entries. Six of them
were files the lane's own session had never touched:

```
src/lib/common/perf/render_perf_receipt_v2.spl
src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl
src/lib/common/crypto/x25519_mlkem768/runner_artifact_provenance.spl
src/lib/gc_async_mut/gpu/browser_engine/style_block.spl
src/lib/skia/entity/geometry.spl
src/lib/common/memory/packed_span.spl
```

All six carry the identical mtime **2026-08-09 04:08:47** — a single bulk write,
not incremental editing. Immediately before launching the run, `find src/lib
src/os -newermt '-5 minutes'` returned **zero** files, so the tree was quiet at
launch and the churn landed mid-flight. This is not the lane's own edits
tripping its own gate, and it is not an architecture-flavoured file.

## Why the current design cannot hold on a shared tree

The gate's refusal window is `2 x full-tree scan + ~151s build` over 9,469
files. Any session doing VCS work on the same working copy will, sooner or
later, land inside that window. The gate is therefore a function of neighbour
activity rather than of kernel correctness, and it fails **closed** on the whole
run — discarding the boot, the serial log, and every receipt — for a change that
in this instance could not affect the artifact at all.

## Suggested fix (not implemented here)

Narrow the manifest from "all of `src/lib`" to the kernel's **actual linked
input set**, which the lane can already determine: the admitted
`build/simpleos_wm_production_desktop.elf` is the authority for which modules
contribute symbols, and the existing comment records that such an `nm` sweep was
already run once to justify the arch prune. Hashing the contributing set instead
of the whole subtree keeps the guard's real purpose (refuse a kernel whose
inputs moved mid-build) while making it immune to unrelated neighbour writes.

A weaker but much cheaper mitigation: on a post-build mismatch, re-check whether
any differing path is in the linked set, and downgrade to a warning when none
is — preserving the boot and the receipts rather than discarding them.

## Impact

Blocked the third of three attempts to run the `props=0` stage discriminator
probe in `CssVarResolutionState.new`. The decisive stage-1/2/3 receipt was only
obtained because an earlier attempt happened to fall in a quiet window. See
`doc/08_tracking/bug/text_index_of_on_substring_receiver_reported_bool_2026-08-09.md`.
