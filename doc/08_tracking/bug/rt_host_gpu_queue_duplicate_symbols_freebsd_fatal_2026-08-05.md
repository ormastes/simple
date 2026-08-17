# `rt_host_gpu_queue_*` duplicated between C and Rust — fatal under FreeBSD's `lld`

- **Re-verified by content 2026-08-17 (os/runtime lane):** `src/compiler_rust/runtime/build.rs` lists `"runtime_native_gpu_stub.c"` and no literal `"runtime_native.c"` c_source entry (grep shows the name only inside explanatory comments at lines 148-184). Both per-lane implementations are still present as intended: 20+ `rt_host_gpu_queue_*` definitions in `src/runtime/runtime_native.c` and 10 `pub extern "C" fn rt_host_gpu_queue_*` in `src/compiler_rust/runtime/src/host_gpu_lane.rs`. The guard spec `test/01_unit/compiler/backend/runtime_native_gpu_stub_duplicate_symbol_guard_spec.spl` exists. The in-guest FreeBSD link was NOT re-run in this lane.

**Found by:** Lane B (FreeBSD WM seam), 2026-08-05, while trying to link
`simple-runtime` inside a real FreeBSD 14.4-RELEASE QEMU guest per
`.claude/rules/board-runnable.md`. Board-run is currently **blocked** by this
defect, not by anything in Lane B's own scope (`src/os/compositor/`,
`src/lib/nogc_async_mut/wm/`).

## The defect

Five symbols are defined **twice**, once in C and once in Rust, both `extern
"C"`-linked into the same `simple-runtime` staticlib:

| symbol | C definition | Rust definition |
|---|---|---|
| `rt_host_gpu_queue_complete` | `src/runtime/runtime_native.c:716` | `src/compiler_rust/runtime/src/host_gpu_lane.rs:290` |
| `rt_host_gpu_queue_drain` | `runtime_native.c:734` | `host_gpu_lane.rs:310` |
| `rt_host_gpu_queue_packet_count` | `runtime_native.c:777` | `host_gpu_lane.rs:337` |
| `rt_host_gpu_queue_submitted_count` | `runtime_native.c:778` | `host_gpu_lane.rs:342` |
| `rt_host_gpu_queue_completed_count` | `runtime_native.c:779` | `host_gpu_lane.rs:347` |

Both sides implement independent, non-trivial queue state (separate static
counters/backing storage on each side) — this is not a stale stub that can be
deleted without checking which copy callers actually need live.

## Why it was invisible until now

GNU `ld` (the default linker on this Linux dev host) tolerates duplicate
strong symbol definitions across translation units in a way FreeBSD's default
`lld` does not — same shape as
[[reference_muldefs_makes_duplicate_symbols_silent_not_fatal]]. `cargo build
-p simple-runtime` links clean on Linux; the identical source tree fails at
link time in the FreeBSD guest with `cargo exit=101`, duplicate symbol errors
naming exactly these five names.

## Impact

- FreeBSD `simple-runtime` cannot link at all — blocks every board-runnable
  claim for the WM/GUI/2D lane on FreeBSD (task #60).
- Likely also fatal on any other `lld`/`mold`-default host (macOS `ld64`
  behavior unverified) — worth checking before assuming this is FreeBSD-only.
- Not fatal on the Linux dev host today only because of linker tolerance, not
  because the duplication is safe.

## Resolution (2026-08-05) — NOT a delete-one-copy fix

Investigated the "suggested fix shape" above (delete `runtime_native.c`'s
copy, keep `host_gpu_lane.rs`) before acting on it, per
[[reference_a_fix_labelled_commit_can_be_a_tree_wipe]] — diff both directions
before deleting either side. That investigation found the suggested shape was
**wrong**: the two copies are not stale-vs-real, they back two different,
never-coexisting lanes, and deleting either would break real callers.

**Both copies are load-bearing, for different consumers, and must stay:**

- `runtime_native.c`'s copy backs **native-compiled (AOT) Simple
  executables**: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  lowers `target.later() gpu|host:` blocks to calls against
  `rt_host_gpu_lane_event`/`rt_host_gpu_queue_emit` (this C ABI family), and
  `src/compiler/70.backend/backend/runtime_compiler.spl` unconditionally
  includes `runtime_native` in the native-product-build C source bundle.
  Those standalone output binaries embed no Rust runtime at all, so they
  need their own C implementation of the primitive.
- `host_gpu_lane.rs`'s copy backs the **Rust-hosted seed/compiler binary's
  own interpreter and JIT** execution of the same lane markers (see
  `interpreter/_EvalOps/call_method_eval.spl`) and carries its own unit
  tests (`cargo test -p simple-runtime --lib host_gpu_lane`, 7/7 green).

**The actual FreeBSD-blocking hazard was narrower than "both defined twice in
the same staticlib" and has already been fixed as a side effect of an
unrelated commit landed the same day.** `src/compiler_rust/runtime/build.rs`
(`compile_c_runtime_sources`) is the file that decides what the
`simple-runtime` crate — and therefore `cargo build -p simple-driver --bin
simple`, the exact command `check-freebsd-wm-seam-refusal.shs` runs in-guest —
actually links. As committed, that function has **never** compiled the full
`runtime_native.c`; before commit `7eb0f507702a` (lane R2,
"fix(interp): register rt_opengl_*/rt_oneapi_* externs", same day) it wasn't
in the list at all (which is why `rt_opengl_*`/`rt_oneapi_*` were unreachable
from the interpreter — a separate bug). R2's fix added
`src/runtime/runtime_native_gpu_stub.c`, a narrow verbatim extract of just
the `rt_opengl_*`/`rt_oneapi_*` bodies, specifically **because** compiling the
whole `runtime_native.c` file would duplicate-symbol against
`host_gpu_lane.rs`'s `rt_host_gpu_*` family — R2's own commit message names
this exact hazard. A stray `runtime_native.o` left over in one `OUT_DIR` from
an intermediate WIP state (mtime before the fix) is consistent with this
being the same failure Lane B observed, from a transient state of the tree
already superseded by the time this doc's fix landed.

**Verified (2026-08-05, this fix):**

- Static: `ar t libruntime_sffi_c.a` for a fresh `cargo build -p
  simple-driver --bin simple` lists 15 members, no `runtime_native.o`.
- Sabotage RED: temporarily added `"runtime_native.c"` back to
  `compile_c_runtime_sources()`'s `c_sources` and forced
  `RUSTFLAGS="-C link-arg=-fuse-ld=lld"` (lld is FreeBSD's default linker,
  unlike this dev host's GNU ld). Link failed with 24
  `rust-lld: error: duplicate symbol: rt_host_gpu_*` errors — the whole
  family, not just the five named above — reproducing the reported failure
  shape locally on Linux by forcing the stricter linker.
- Sabotage GREEN: reverted the one-line addition; `cargo build -p
  simple-driver --bin simple` under the same forced `lld` linker finished
  clean (`Finished dev profile ... in 1m 46s`), no duplicate-symbol errors.
- `cargo test -p simple-runtime --lib host_gpu_lane`: 7 passed, 0 failed.
- Added a regression guard,
  `test/01_unit/compiler/backend/runtime_native_gpu_stub_duplicate_symbol_guard_spec.spl`,
  asserting `build.rs` never re-adds a literal `"runtime_native.c"` C-source
  entry (only the extracted stub) and that both per-lane implementations stay
  present. Sabotage/revert re-verified green (2 examples, 0 failures) and red
  (1 of 2 failed) against this spec directly.

## Verification once fixed — CONFIRMED on real FreeBSD hardware proxy

Re-ran `scripts/check/check-freebsd-wm-seam-refusal.shs` inside a real
FreeBSD 14.4-RELEASE QEMU guest (`build/freebsd/vm/`, real BASIC-CLOUDINIT
boot, KVM accel, no `-kernel`/`isa-debug-exit`, per
`.claude/rules/board-runnable.md`). Previously this exited non-zero with
`refusal=blocked reason=in-guest build did not complete`. This run:

- `cargo build -p simple-driver --bin simple` **linked cleanly in-guest**
  (`Finished dev profile [unoptimized + debuginfo] target(s) in 4m 39s`) — no
  duplicate-symbol errors, confirming the fix holds on the real `lld`-default
  target this bug was filed against, not just under a forced-`lld` simulation
  on the Linux dev host.
- The probe then ran the actual in-guest interpreter against the real
  `wm_host_2d_for("freebsd")` seam and printed:
  `FREEBSD WM SEAM VERDICT: platform=freebsd refusal=yes reason=VM harness
  boots but no 2D backend exists for this platform`
- Final line: `FreeBSD WM seam refusal check PASSED`.

The `refusal=yes reason=... no 2D backend exists` outcome is the correct,
expected verdict for a separate, already-known non-goal (FreeBSD has no 2D
compositor backend yet) — not a build failure. Task #60's board-runnable
blocker from this duplicate-symbol bug is cleared; the WM/GUI/2D lane on
FreeBSD is unblocked to proceed on its own merits.
