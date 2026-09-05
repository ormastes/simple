# SimpleOS-WM freestanding kernel link now blocked by 4 NEW unbaselined fabricated symbols (2026-07-31)

## Status

OPEN. This is a **different, earlier** blocker than the two previously
recorded for showcase cell #7 (`SimpleOS-WM × QEMU`): the missing-vtable
`ud2` trap (`native_with_trait_impl_no_vtable_duck_trap_2026-07-28.md`) and
the pointer-release font-metrics hang
(`simpleos_wm_pointer_release_font_metrics_hang_2026-07-26.md`). Neither of
those can be exercised right now because the kernel **fails to link**, so
QEMU never boots.

## Provenance check performed first

`git merge-base --is-ancestor f2f64a137bd9518c06ea33236ecc16504a73830a
465ec1cd34345fd7be512289c14ebccc3918ffe0` returns true (exit 0): the 2026-07-28
vtable-trap source fix **is** an ancestor of origin `main` tip
`465ec1cd334`. That prior finding stands. It just isn't the thing blocking
the build right now.

## Reproduction

Fresh detached worktree at origin tip `465ec1cd34345fd7be512289c14ebccc3918ffe0`
(fetched via `git ls-remote` + `git fetch`, never the shared/local WC — that
WC's git HEAD is a `.jjconflict-*` tree with no source). 57 files present
under `assets/fonts` in the worktree (shared WC sparse-checkout trap does not
apply here).

```
SIMPLE_BIN=/home/ormastes/dev/pub/simple/build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
SIMPLE_BIN sha256=c0d1ed629b18fc703bc2671c8a9d9043cd1c705e480d9bf511f03233843342b1
SIMPLE_BIN --version: simple-bootstrap 1.0.0-beta   (existing pure-Simple stage3
  self-host binary; NOT the Rust seed -- no cargo build performed)

BUILD_DIR=<scratch>/cell7_build
REPORT_PATH=<worktree>/doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-31.md
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
  (wrapper sha256=e81fb6cc22c70a4c8350dab0f1bdc55f5cad8ff54feea8694c4c8844ebe7b7e5)
```

Result: `status=fail reason=wm-simple-web-build-failed
kernel_build_status=failed-cache-preserved`. QEMU/OVMF never launched
(`serial_log_bytes=0`); the failure is entirely inside the
`native-build --target x86_64-unknown-none` link step for
`simpleos_wm_production_desktop.elf.candidate`.

## Exact failure

```
Freestanding unresolved symbol check: 124 unexpected symbol(s)
Fabricated freestanding stubs: 124 symbol(s) for entry
  'simpleos_wm_production_desktop.elf.candidate' -- weak bodies that RETURN 0
  (baseline config/freestanding_fabricated_stub_baseline.sdn: 120 known, 4 new)
...
Build failed: freestanding link would FABRICATE 4 symbol(s) not in the
baseline for entry 'simpleos_wm_production_desktop.elf.candidate':
  rt_cuda_device_identity, rt_raw_i64_to_string, rt_string_byte_at,
  rt_vulkan_accepted_compute_submit_count.
These get weak bodies that return 0, which silently corrupts every caller.
```

Full log: `native-build.out` (134 lines), retained at
`<scratch>/cell7_build/native-build.out` (scratch, not committed).

## What the ratchet is and why it fired here

`config/freestanding_fabricated_stub_baseline.sdn` was machine-written at
120(121 incl. one later-removed row per its commit message) known-fabricated
symbols on 2026-07-29 (`b4f496322361696d2b174c71f61a3f568432b3c4`, one day
**after** the vtable fix `f2f64a137bd`). From that commit on, any symbol the
freestanding linker would have to weak-stub for this entry that is **not**
already in the baseline fails the build instead of silently linking a
nil-returning stub — the exact mechanism the doc for
`b4f496322361696d2b174c71f61a3f568432b3c4` says was added because an earlier
fabricated `rt_array_copy` silently shredded every array copy in a guest.

So: between whatever tree the baseline was captured from (`0ecb040da42`) and
current origin tip `465ec1cd334`, the SimpleOS-WM production entry closure
started reaching 4 additional symbols it did not reach before, none of which
have a real freestanding (`x86_64-unknown-none`) implementation.

## Per-symbol notes

- `rt_cuda_device_identity`, `rt_vulkan_accepted_compute_submit_count` — **zero**
  hits anywhere under `src/runtime/**/*.{rs,c,S}` in this tree. No
  implementation exists in any runtime, freestanding or hosted. Consistent
  with the baseline commit's own note that "GPU runtime families (cuda, ...,
  vulkan, ...)" are named debt categories — these two are new members of
  that same family, just not yet baselined.
- `rt_raw_i64_to_string`, `rt_string_byte_at` — **do** have real pure-Simple
  implementations (`src/runtime/simple_core/core_string.spl:875` and `:337`
  respectively). These are reachable from the freestanding entry closure for
  the first time (or reachable via a path the linker didn't previously
  attribute to this entry); why the real implementation isn't satisfying the
  link for this specific entry is unresolved and is the most promising next
  lead, since a working native-runtime implementation already exists.

## Do not weaken the gate

`SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1` would silently accept these 4 as
new debt rows without explaining why nil-returning bodies are safe for them,
which is exactly the failure mode the ratchet exists to prevent (see the
`rt_array_copy` incident cited above). Not applied here.

## Next step

Determine why `rt_raw_i64_to_string` / `rt_string_byte_at` are newly
reachable from `simpleos_wm_production_desktop.elf.candidate`'s freestanding
closure (call-graph diff against tree `0ecb040da42`), and either route those
two through the existing pure-Simple implementations at link time, or
implement real freestanding bodies for the GPU-identity pair (or prove they
are dead code on this entry and can be pruned). Only after the kernel links
again can the two previously recorded blockers (vtable trap — believed fixed
by `f2f64a137bd`; font-metrics hang — unresolved) be re-tested end to end.
