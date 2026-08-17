# AC-4 SIMD byte-identity probe crashes on reproduction — reported PASS does not hold

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
at the `simple-runtime` source level, verified at the Rust-crate/unit level
only — NOT yet verified end-to-end against the named `.spl` probe, which does
not exist in this repo, and NOT yet in the deployed `bin/simple` binary; see
the "2026-08-06 update" section below before treating this as closed). A
dispatched root-cause
agent (session-limit-terminated before delivering a report) apparently left
"both probes healthy" as its last status line, and independent re-testing
now gets 6/6 consecutive PASS on `mlkem_ntt_simd_public_interface_probe.spl`
against the currently-deployed binary. **No source diff explains this** —
every file under `src/runtime/` and `src/compiler_rust/` was diffed against
origin and none contains an alignment-related change; the two files that ARE
modified in this area (`runtime_simd_dispatch.c/.h`) diff to unrelated
OpenCL-probe removals from a different concurrent session's work, not a
`rt_simd_mul_i32x8` fix. The most likely explanation is heap-layout-dependent
nondeterminism (consistent with the original 3x-SIGABRT-then-1x-SIGSEGV
pattern across different binary builds) rather than a genuine fix — the
underlying misalignment condition should be assumed to still exist until a
source-level root cause is found and landed. Re-run the reproduce steps
below under load / after other allocations to check whether it still
recurs before relying on this probe's green status for anything.
**Found:** 2026-08-05
**Severity:** HIGH — a landed campaign claim ("AC-4 x86 lane closed under
`interpret`, `ac4_x86_simd_public_interface_verdict=PASS ... checks_failed=0`")
does not survive independent reproduction; the probe crashes instead.
**Component:** `rt_simd_mul_i32x8` (`src/runtime/src/value/simd_int_ops.rs:705`),
exercised via `test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl`
**Attribution:** measured on the Rust bootstrap seed (`bin/simple` prints the
seed banner); no self-hosted binary exists in this worktree.

## What was claimed

A prior agent this session reported, for `mlkem_ntt_simd_public_interface_probe.spl`
run under `--engine interpret`:

> Verdict: `ac4_x86_simd_public_interface_verdict=PASS ... checks_failed=0`
> ... backend identity confirmed via `mlkem_ntt_simd_receipt().chunk_hits`
> (240/240 SIMD arms, 0/0 forced-scalar) and an independent gdb breakpoint
> instrument (1440 executions of `_mm256_mullo_epi32` in the SIMD arm, 0 in
> forced-scalar).

## What independent reproduction found

Running the **exact same probe file** (md5 `929b93568bcf76d20a76295f129a1b83`,
unchanged) with `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run
test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl
--engine interpret` does not produce a verdict line. It crashes, every time:

- **3/3 runs** against a stale ad-hoc scratch seed build
  (`/tmp/.../scratchpad/simple-fixed`, a leftover debug build from an
  earlier point in this session — see the `bin/simple` symlink note below):
  identical `PANIC misaligned pointer dereference: address must be a
  multiple of 0x4 but is 0x...013d1` at `runtime/src/value/simd_int_ops.rs:705:13`,
  `thread caused non-unwinding panic. aborting.`, exit 134 (SIGABRT). The low
  address bits (`...013d1`) were identical across all 3 runs despite ASLR
  varying the high bits — a structural misalignment, not a random fluke.
- **1/1 run** against the correct, canonical binary
  (`bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, restored
  after finding the symlink had been pointing at the stale scratch build —
  see `doc/08_tracking/bug/bin_simple_symlink_pointed_at_stale_scratch_build_2026-08-05.md`):
  `Segmentation fault`, exit 139 (SIGSEGV). Different signal, same call site
  family (native SIMD intrinsic dereferencing a marshalled pointer), still a
  crash, not a verdict line.

So the crash is **not** an artifact of the wrong/stale binary — it reproduces
on the correct one too, just with a different fault (SIGSEGV vs SIGABRT,
plausibly because the two binaries were built with different
optimization/debug profiles that change heap layout around the same
underlying misalignment bug). md5 of the probe file was identical
before/after every run; not contamination.

## What this means for AC-4

The claimed PASS for the x86 SIMD lane through the public interface **does
not hold**. This bug doc supersedes that claim until the crash is fixed and
the probe is re-run and independently reproduced green. The forced-scalar
control probe (`mlkem_ntt_forced_scalar_control_probe.spl`) does run
successfully (`ac4_scalar_control_verdict=RAN forward_len=768 inverse_len=768`)
— only the SIMD arm crashes, which is at least consistent with a genuine
SIMD-path defect rather than a fixture problem.

## Not yet root-caused

This doc records the discrepancy and reproduction evidence; it does not
diagnose why `rt_simd_mul_i32x8` receives a misaligned pointer here when
earlier, narrower SIMD evidence in this campaign (the standalone AVX2
constant-multiplication probes referenced elsewhere in this session) did
not hit this fault. Next step: read `simd_int_ops.rs` around line 705 and
trace the allocation path for the array this probe constructs, under
`--engine interpret`, to find where the returned pointer loses its required
4-byte alignment.

## Reproduce

```
md5sum test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl
SIMPLE_TIMEOUT_SECONDS=0 bin/simple run \
  test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl \
  --engine interpret
echo "exit=$?"   # expect 139 (SIGSEGV) or 134 (SIGABRT), not a verdict line
```

## 2026-08-06 update — root cause found and fixed at source level; NOT independently closed end-to-end

**Status: PARTIALLY ADDRESSED — do not mark this doc FIXED/CLOSED yet.** Read
the whole section before trusting this. Given this doc's own history (a false
"both probes healthy" claim that didn't survive re-check), this update is
deliberately conservative about what was and wasn't verified.

### The probe fixture files do not exist in this repository — a new finding

Before touching any code, an attempt was made to run the exact repro command
above. It failed immediately:

```
bin/simple run test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl --engine interpret
# error: No such file or directory
```

Neither `mlkem_ntt_simd_public_interface_probe.spl` nor
`mlkem_ntt_forced_scalar_control_probe.spl` exist in the working tree. A
search of `git log --all -- <path>` for both files returns **no history at
all** — they were never committed to this repo, ever. A further search across
every scratch worktree and agent scratchpad directory found on this machine
(`/tmp/claude-1000/.../scratchpad/**`, `/tmp/simple-*`,
`.claude/worktrees/**`, `build/worktrees/**`, `build/bootstrap-segv-fix/**`) —
dozens of copies of this exact bug doc and the sibling
`mlkem_ntt_simd_c_test.c` fixture were found, but **zero copies of either
`.spl` probe file**, anywhere. The most likely explanation: both probes were
always ephemeral scratch files created directly in some prior agent's
scratchpad or `/tmp`, never `git add`ed, and were cleaned up or lost when that
session ended. This means **the literal repro steps in this doc have never
been independently re-runnable by any agent after the one that wrote them**,
including this one. Anyone re-checking this doc in the future should expect
the same and not be surprised the fixture is gone — this is not evidence
against the crash having been real.

Because of this, **step 4 of the requested verification plan (re-run the
named `.spl` probe 5-10 times and read its verdict line) could not be
performed at all** — there is no fixture to run. What follows is the
strongest verification that was achievable without recreating that fixture
from scratch (which would risk not matching what the original probe actually
exercised).

### Root cause (confirmed, independently reproduced, decoupled from this crate)

`rt_simd_mul_i32x8` and seven sibling functions in
`src/compiler_rust/runtime/src/value/simd_int_ops.rs` — all eight
`rt_simd_{add,sub,mul,xor,and,or,shl,shr}_i32x8` `#[no_mangle] pub extern "C"`
wrappers (`add`/`sub`/`mul`/`xor`/`and`/`or` at their original lines
642/672/702/732/762/792, `shl`/`shr` at 822/842) — read/wrote through their
`*const i32` / `*mut i32` parameters with a **plain Rust pointer
dereference**: `*a.offset(i)` and `*out.add(i) = val`. `rt_simd_mul_i32x8`'s
read block began at the original line 705 — the exact file:line cited in the
original report.

A plain `*ptr` dereference of a typed pointer lowers to `ptr::read`/
`ptr::write`, both of which carry Rust's alignment precondition (the pointer
must be a multiple of the pointee's alignment — 4 bytes for `i32`). This is
**not** an AVX2/`_mm256_load_si256` hardware alignment requirement (the
in-file SIMD helper `mul_i32x8([i32;8],[i32;8])` already correctly used the
unaligned `_mm256_loadu_si256`/`_mm256_storeu_si256` intrinsics on its own
stack-local arrays, which is why the C test fixture and narrower probes never
hit this) — it is Rust's own UB-check on the *raw pointer marshalling step*
that happened before the caller-supplied `a`/`b`/`out` pointers ever reached
any SIMD instruction. Callers of these `extern "C"` functions (native/JIT
codegen emitting a direct call with a pointer derived from Simple-side
array/Value storage, or an FFI/SFFI caller) do not guarantee 4-byte alignment
on that storage — see the closely related, same-day
`doc/08_tracking/bug/rt_array_data_ptr_u8_missing_interpreter_adapter_2026-08-05.md`,
which documents the exact mechanism by which an interpreter-native
`Value::Array` gets materialized into a leaked `Vec<u8>` and handed out as a
raw pointer with no i32-alignment guarantee — a plausible concrete path by
which a misaligned pointer reaches these functions.

**Independent, decoupled confirmation of the exact mechanism and message**
(done outside this crate, in a standalone `rustc`-compiled program, to rule
out anything crate-specific): allocating a `Vec<u8>`, offsetting it by 1-3
bytes to force a misaligned `*mut i32`, and doing `*p.offset(0)` on it:
- Under a **debug build** (`debug_assertions` on — matches a `cargo build`
  without `--release`, i.e. plausibly the "stale ad-hoc scratch seed build"
  from the original report): panics with **the exact same message**,
  `misaligned pointer dereference: address must be a multiple of 0x4 but is
  0x...`, followed by `thread caused non-unwinding panic. aborting.` — a
  **non-unwinding** abort, meaning `catch_unwind` cannot intercept it, which
  is consistent with the original report's SIGABRT/exit 134.
- Under an **optimized build** (`rustc -O`, `debug_assertions` off — plausibly
  the "canonical release binary" from the original report): the alignment
  check is compiled out entirely; the read silently returns without panicking
  (observed returning a garbage/zero value rather than crashing in this
  isolated repro). This is consistent with — though does not by itself fully
  explain — why the release binary in the original report produced a
  *different* crash signature (SIGSEGV) rather than the clean debug panic:
  the underlying access is still UB in the optimized build, just not
  checked, so a fault can still occur downstream depending on what
  instruction selection the optimizer chose around the "pointer is aligned"
  assumption it's now permitted to make.
- The replacement (`.read_unaligned()`/`.write_unaligned()`) never panicked
  and always returned the correct value, in both build profiles, across 5
  repeated runs x 3 misalignment offsets (shift 1/2/3 bytes) = 15/15 clean.

### Fix applied

All 8 affected functions in `simd_int_ops.rs` changed from
`*ptr.offset(i)` / `*out.add(i) = val` to `ptr.offset(i).read_unaligned()` /
`out.add(i).write_unaligned(val)`. This matches the unaligned-load precedent
already established in the same file for the actual SIMD hardware
instructions and makes every one of these FFI entry points correct
regardless of what alignment the caller's marshalling path happens to
produce, rather than requiring every caller (interpreter array materializer,
JIT/native codegen, any future SFFI caller) to separately guarantee 4-byte
alignment. A `#[cfg(test)]` regression test was added
(`rt_simd_mul_i32x8_misaligned_pointer_does_not_panic` and
`rt_simd_add_sub_xor_and_or_shl_shr_i32x8_misaligned_pointer_does_not_panic`)
that deliberately constructs misaligned pointers (byte shift 1/2/3 from a
byte buffer, so the misalignment is created by test construction, not
allocator luck — this specifically avoids the "heap-layout-dependent
nondeterminism" trap this doc already warned about once) and calls all 8
functions through their real `extern "C"` signatures.

### Verification performed (Rust-crate level; T1-scoped per bootstrap.md)

- `cargo build -p simple-runtime` (in `src/compiler_rust`): clean build, no
  warnings introduced.
- `cargo test -p simple-runtime --lib simd_int_ops`: run twice (once
  immediately after the fix, once again after adding the two new regression
  tests). **21/21 passed both times**, including the two new misalignment
  tests, each of which loops over 3 distinct forced-misalignment offsets
  across all 8 functions (48 assertions total per full run).
- Standalone decoupled repro (above): 5 runs of the "does NOT panic" case, 3
  offsets each, 100% consistent (15/15); 1 run of the "DOES panic on old
  code" case in a debug build, reproducing the exact panic text and abort
  signal from the original report on the very first try (not
  heap-layout-dependent, because the misalignment here is constructed
  deterministically by byte-shifting a pointer, not left to allocator luck).

### What was explicitly NOT verified — read this before trusting "fixed"

- **The named `.spl` probe was never re-run**, because it does not exist
  (see above). This doc's own reproduce steps remain, today, exactly as
  unreproducible as they were when this update was written — the only
  difference is now there's an explanation why (missing fixture), not a
  crash-vs-no-crash result.
- **`bin/simple` (the deployed seed binary) was not rebuilt or redeployed.**
  Per `.claude/rules/bootstrap.md` T0-T3 tiering and this task's explicit
  scope ("verify with a scoped `cargo build -p <crate>`... NOT a full
  bootstrap"), only the `simple-runtime` crate itself was built and tested in
  isolation. `bin/release/x86_64-unknown-linux-gnu/simple` — the binary
  `bin/simple run ... --engine interpret` actually executes — still links
  the **old**, unfixed `simd_int_ops.rs` until a bootstrap rebuild + redeploy
  happens. Anyone re-checking this by literally running `bin/simple run
  <probe>` today, even if the probe existed, would NOT be exercising this
  fix yet.
- **The exact call path that reached this function under `--engine
  interpret` in the original report is still not fully pinned down.** Tracing
  `interpreter_extern::simd::rt_simd_mul_i32x8`
  (`src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1084`) shows
  that `std.simd`'s registered dispatch for this name calls `binop_i32x8`,
  which unpacks interpreter `Value`s into a plain `[i32; 8]` Rust array by
  value and calls the **safe**, non-pointer `mul_i32x8([i32;8],[i32;8])`
  helper — it does **not** call the raw-pointer `extern "C"` wrapper this fix
  changed. That means a Simple program calling `std.simd`'s public
  `rt_simd_mul_i32x8` under `--engine interpret` cannot hit this bug through
  that specific path. The original probe must therefore have reached the raw
  `extern "C"` symbol some other way — e.g. a bare `@extern fn
  rt_simd_mul_i32x8(...)` declaration in the (now-missing) probe bypassing
  `std.simd`'s wrapper and calling the native symbol directly via SFFI/dynamic
  load, which is exactly the kind of "public interface" boundary test an
  AC-4 x86-SIMD-lane-closure probe would plausibly want to exercise. This is
  plausible and consistent with the file:line/message match being exact, but
  it was not confirmed by tracing an actual working example, because no such
  example exists in this repo to trace.

### Honest confidence assessment

High confidence that a real bug existed at the exact cited function, file,
and line, with the exact cited panic message and abort behavior — this was
independently reproduced from first principles, not just inferred. High
confidence the fix (`read_unaligned`/`write_unaligned`) is the correct and
complete fix for that specific defect, verified by both targeted crate tests
and a decoupled standalone repro across two build profiles. **Low-to-moderate
confidence that this closes the original report's exact end-to-end
symptom**, because the probe that produced that symptom cannot be re-run (it
doesn't exist) and the deployed binary hasn't been rebuilt with this fix. Do
not mark AC-4's x86 SIMD lane claim PASS on the strength of this update
alone — the next step to actually close this is (a) rebuild+redeploy
`bin/simple` via bootstrap, and (b) either recover or faithfully recreate the
missing probe fixture and run it 5-10 times against the redeployed binary,
exactly as the original (untrusted) "PASS" claim should have been checked in
the first place.

## Re-confirmed 2026-08-09

Re-read in full. `src/compiler_rust/runtime/src/value/simd_int_ops.rs` was
inspected fresh: all eight `rt_simd_{add,sub,mul,xor,and,or,shl,shr}_i32x8`
wrappers already use `.read_unaligned()`/`.write_unaligned()` (e.g. line 645
onward), confirming the 2026-08-06 source-level fix is landed and present on
the current tree. The named probe files
(`mlkem_ntt_simd_public_interface_probe.spl`,
`mlkem_ntt_forced_scalar_control_probe.spl`) still do not exist anywhere in
this working copy, so the literal end-to-end repro remains not independently
re-runnable, matching the 2026-08-06 finding exactly. Per the mandate here,
`src/compiler_rust/**` may not be edited from this pass and a full bootstrap
rebuild+redeploy is out of budget for a single item, so this stays
**ARCHITECTURAL-OPEN**: the source fix is real and present, but the
end-to-end claim cannot be independently closed without (a) a Stage
rebuild/redeploy of `bin/simple` and (b) recreating the missing `.spl`
fixture. No code touched.

## Re-verified 2026-08-17 (worker s3_rust_other) — SPLIT

- **Alignment crash: ALREADY-FIXED.**
  `src/compiler_rust/runtime/src/value/simd_int_ops.rs` `rt_simd_mul_i32x8`
  now uses `read_unaligned()` (with a comment citing this bug doc), and
  `mul_i32x8` (:379-390) uses `_mm256_loadu_si256`/`storeu`. No aligned
  `_mm*_load_si*` intrinsic remains in the file.
- **Reported PASS still unsupported: LIVE.** The named probe
  `test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl`
  still does not exist; that directory holds only
  `mlkem_avx2_reduce_selfcheck.c` and `mlkem_ntt_simd_c_test.c`. Keep open for
  the missing probe only.
