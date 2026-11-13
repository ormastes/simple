# Four new single-lane `rt_vulkan_*` symbols block every push
## Fixed 2026-11-13

**Status:** FIXED — the symbols are twinned and the push gate no longer blocks on inherited debt
**Found:** 2026-09-05, while pushing an unrelated lane

### Resolution evidence (measured 2026-11-13 on `release/1.0.0` at `073fe2a89dd`)

1. **The original four are no longer single-lane.** The four symbols were
   `rt_vulkan_copy_u32_slots`, `rt_vulkan_readback_u32_checksum`,
   `rt_phase_profile_record` and `rt_to_int_dynamic` (named in
   `rt_dual_ratchet_red_at_origin_four_unbaselined_symbols_2026-09-06.md`;
   only two of the four are `rt_vulkan_*`, despite this record's title).
   - `rt_vulkan_copy_u32_slots`: C twin `src/runtime/runtime_native.c`
     (`int64_t rt_vulkan_copy_u32_slots(...)`), Rust
     `vulkan_graphics_runtime_buffer.rs`.
   - `rt_vulkan_readback_u32_checksum`: weak C twin in
     `src/runtime/runtime_native.c`, Rust `vulkan_graphics_runtime_buffer.rs`.
   - `rt_to_int_dynamic`: C `src/runtime/runtime_native.c`, Rust
     `src/compiler_rust/runtime/src/value/collections.rs`.
   - `rt_phase_profile_record`: C `src/runtime/runtime.c`, Rust
     `src/compiler_rust/native_all/src/mem_snapshot_provider.rs`.

   None of the four appears as a baseline row, in the ratchet's NEW list, or in
   its STALE list, i.e. the ratchet classifies all four as dual-lane.
2. **The push gate is delta-based.** Since 2026-09-23 `push-rt-dual-implementation`
   compares the pushed tip against the commit the push replaces
   (`--baseline-rev`); only a symbol that is single-lane at the tip and not at
   the base is fatal. Inherited debt cannot block an unrelated push any more
   (`.claude/rules/vcs.md` § "Push tier minimised").
3. **The one remaining single-lane `rt_vulkan_*` symbol is now twinned.**
   `rt_vulkan_selected_device_identity_v1` had a Rust lane
   (`vulkan_graphics_runtime_device.rs`) and no C lane. A weak C twin was added
   next to the readback twin in `src/runtime/runtime_native.c`. The core C
   runtime selects no Vulkan device, so it returns the empty string, matching
   the Rust `cfg(not(feature = "vulkan"))` arm; the Simple facade
   `vulkan_sffi_selected_device_identity_v1` requires `v1:<hex>:<hex>` and
   rejects it with "selected Vulkan physical device identity unavailable".
   No baseline row was added, removed or regenerated.

   ```
   before: FAIL — 2779 symbol(s) checked against 2490 baselined, 409 new, 120 stale
   after:  FAIL — 2778 symbol(s) checked against 2490 baselined, 408 new, 120 stale
   ```

   The only line that differs between the two full reports is
   `rt_vulkan_selected_device_identity_v1` leaving the NEW list.
   `clang -fsyntax-only src/runtime/runtime_native.c`: 0 errors. (The whole-tree
   `check-c-runtime-compiles-push.shs` is red on this aarch64 host for 20
   unrelated files — x86 vector providers, darwin/windows selfchecks — and
   `runtime_native.c` is not among them.)
   `backend_vulkan_showcase_frame_parity_spec.spl`: 4 passed, 0 failed — a
   no-regression check only: the seed runs the Rust lane and does not call
   the C twin.
4. **Not in scope, still red:** the frozen full ratchet (408 new / 120 stale
   after this change) is repo-wide single-lane debt across many subsystems. It
   is informational at push and enforced by the extended CI job; it is not this
   bug and is not closed by it.

The original report follows unchanged.

## Symptom

```
$ sh scripts/check/check-rt-dual-implementation-ratchet.shs
FAIL — 2492 symbol(s) checked against 2488 baselined, 4 new, 0 stale
  ... rt_vulkan_copy_u32_slots
      rt_vulkan_readback_u32_checksum
```

`push-rt-dual-implementation` is a **blocking** push-tier row
(`config/check/must_check_gates.sdn:21`), so this fails every `git push` from
this repository regardless of what the pushing lane changed. It is tree-scoped,
not range-scoped.

## Not the pushing lane's doing

Reproduced on the untouched main working tree (same verdict, same four symbols),
and on a cherry-pick range that touches no `.c`, `.rs`, or runtime file at all.
The failure is inherited from committed content, not introduced by a push.

## What is actually missing (measured, not assumed)

The four symbols are NOT absent everywhere. `rt_vulkan_copy_u32_slots`, for
example, exists in three places:

```
src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:571  pub extern "C" fn rt_vulkan_copy_u32_slots(
src/compiler_rust/compiler/src/interpreter_extern/vulkan.rs:165      ("rt_vulkan_copy_u32_slots", Ret::I, "vvi"),
src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:83                extern fn rt_vulkan_copy_u32_slots(...)
```

So there is a Rust implementation, an interpreter extern registration, and a
Simple declaration. What is missing is the **C lane** — which is precisely the
axis `check-rt-dual-implementation-ratchet.shs` measures. A reader who greps for
the symbol will find it and conclude the gate is wrong; it is not.

## Why the baseline must NOT simply be regenerated

The guard's contract is that an `rt_*` symbol exists in BOTH the C and Simple
lanes. A symbol implemented in Rust but not C is exactly the gap the ratchet
exists to catch. Running `--generate-baseline` would record the single-lane state as
accepted debt and launder exactly what was caught — the same anti-pattern
`.claude/rules/vcs.md` warns about for the divergence and unbacked-extern
ratchets.

The correct fix is one of:
- implement the missing lane for all four symbols, or
- remove them if the lane that added them no longer needs them, or
- a reviewed, deliberate baseline update by **the lane that added them**, with the
  reason recorded.

Whoever added the `rt_vulkan_*` work owns this call. It is not a decision an
unrelated lane should make by regenerating a baseline to unblock itself.

## Interim

Until it is resolved, every push from this repo either fails or is forced with
`--no-verify`, which nullifies all 18 push-tier gates rather than just this one.
That is a much worse state than one red gate, and is the reason this record
exists rather than a silent workaround.

