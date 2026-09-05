# WM evidence lane: source-hash gate trips on a foreign session's bulk `src/lib` write

## Status

**FIXED 2026-08-09** in `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
— see "Resolution" at the bottom. Originally an open blocker; reproduced
2026-08-09 with a named, timestamped cause. This was the gate that made the
SimpleOS WM lane unrunnable on a shared working tree.

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

## Suggested fix (as originally filed; see Resolution below for what shipped)

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

## Resolution (implemented 2026-08-09)

The suggested fix was taken, with one strengthening: the linked-symbol set is
used as a **repair** on top of a primary definition, not as the definition
itself, because a file can change the artifact without contributing a symbol.

The hashed set is now the kernel's actual input set, defined two independent
ways and UNIONED (a union can only widen, so it cannot fail open):

1. **Import closure** — the transitive `use` closure of the real compiler
   inputs: the `--entry` file plus every file under the `--source` directory
   `build/os/generated`. Module resolution mirrors the compiler's rules (`std.`
   → `src/lib`, tier-relative and tier-fallback lookups, `dir/mod.spl`,
   sibling-relative). Where a module path cannot be resolved exactly, **every**
   file whose basename matches is admitted — ambiguity always widens the set.
   Cross-check: the build reports `5 compiled, 750 cached` = 755 modules; the
   closure resolves 1,313 files, a superset of what the compiler compiled.
2. **Linked-symbol repair** — `nm --defined-only` on the kernel ELF yields the
   symbols the artifact genuinely links. Any file *outside* the closure that
   defines a linked symbol which *no* closure file defines is added. This
   repairs a resolver gap using the built artifact itself rather than trusting
   the resolver. The measured gap before the repair existed was 7 symbols
   (`serial_println`, `bytes_to_string`, `_heap`, `floor`, `is_whitespace`,
   `rt_time_now_unix_micros`, `_fat32_next_cluster`); the repair closes it.
3. All non-`.spl` link inputs (193 `.c/.h/.s/.S/.ld` files) under the same roots
   are hashed unconditionally — few, load-bearing at link time, not churning.

**1,512 files hashed instead of 9,608.** The file list is computed once per run
and reused for the before/after hashes, so a mid-build edit to a listed file
always changes the revision. The old per-file `sha256sum` fork loop (~24s per
scan) is unchanged in form but now runs over 1/6 as many files.

### Fail-closed properties (do not weaken)

- Empty / too-small input set → ERROR, never a pass (`KERNEL_INPUT_MIN_FILES`
  floor, default 200, plus the entry file must appear in its own input set).
- Any file that fails to hash to a sha256 → ERROR.
- Missing source root → ERROR.
- Manifest line count ≠ resolved file count → ERROR.
- The set is only ever widened by ambiguity, never narrowed.

### Verdict strings

Matching the pre-push-guard convention, a passing verdict always states how many
files it actually hashed, so a vacuous run cannot be mistaken for a real one:

```
simpleos_wm_kernel_input_verdict=PASS — 1512 file(s) hashed (set=closure+linked-symbol-repair, revision=<sha256>)
simpleos_wm_kernel_input_verdict=FAIL — kernel input source changed during build (1512 file(s) hashed, set=closure+linked-symbol-repair)
simpleos_wm_kernel_input_verdict=ERROR — nothing was checked (kernel input set unresolved: <status>)
```

`evidence.env` additionally carries
`simpleos_wm_fullscreen_kernel_source_input_files` and
`simpleos_wm_fullscreen_kernel_source_input_set`. The kernel admission record is
bumped to `schema=simpleos-wm-kernel-admission-v2` and pins
`source_input_files=<n>`, so a v1 admission is stale and forces a rebuild.

### Proof (both directions)

`sh test/system/simpleos/wm_kernel_input_set_gate_test.shs` — 16 checks, all
passing. It exercises the shipped code (the functions are extracted from the
gate script itself, not copied), and never writes under `src/**` — writing there
is the very defect under repair.

| check | result |
|-------|--------|
| old whole-tree hashed set | 9,608 files |
| new kernel input set | 1,512 files (`closure+linked-symbol-repair`) |
| `src/os/compositor/compositor.spl` (linked) | IN |
| `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session.spl` (the churn set) | OUT |
| write to an unrelated source mid-window | revision **unchanged** — no abort |
| write to a linked source mid-window | revision **changed** — gate still refuses |
| missing source root | count 0, empty revision, ERROR verdict |
| input set below the vacuity floor | count 0, never a pass |

Of the six foreign-written files named in the Evidence section above, the two
under `gpu/engine2d/` and `gpu/browser_engine/` are exactly the class the new set
excludes; none of the six is reachable from the WM entry's import closure.
