# 42 unit-spec exclusions: measured timeout classification and partial optimization (2026-08-27)

Status: OPEN. This change removes one COW alias hot path in the
`nogc_sync_mut` JS interpreter. It does not resolve or close the excluded
specs. The 4096-handle timer workload still has an O(total²) property scan.

**All 42 listed specs are now measured.** Of the 40 real specs, 24 time out
without a completed verdict at 900s, 8 finish inside 900s, and 8 fail in
seconds. The timeout data does not by itself prove that a spec is hung. See
§2e.

Evidence binary (identical for every measurement from the 2026-08-27 sweep
recorded below, re-stat'd after the sweep and unchanged):
`bin/release/x86_64-unknown-linux-gnu/simple`, size `60744944`,
mtime `2026-08-26 01:16:25 +0000`. Re-stat before comparing to these numbers —
the symlink target is replaced by other agents mid-session.

Method: each spec run alone from a detached worktree at `origin/main`
(`2b35049f8d7`) with `timeout 900 bin/simple test <spec>`, 4 concurrent.
Concurrency inflates wall times, so a *finishing* time here is an upper bound;
a 900s row is a timeout regardless.

Fixed startup cost was measured first and ruled out as the cause: a trivial
spec (`test/01_unit/bugs/cast_else_swallows_outer_if_spec.spl`) completes in
**6s**. These specs are not startup victims.

## 1. Count reconciliation: 42 listed, 40 real

Two of the 42 names are generated `.spipe_*` scratch artifacts, not tracked
specs. Neither exists in the tree at `origin/main`:

- `test/01_unit/lib/common/text_layout/.spipe_cov_2280333_1787707528425676_font_renderer_spec.spl`
- `test/01_unit/os/kernel/memory/.spipe_wrapped_entry_vmm_copyin_spec.spl`

They are transient coverage/wrapper files written by the spipe runner and
swept up by whatever enumerated the failing set. The first was run anyway and
exits in 3s with rc=1 (file not found). They should be excluded from the
hang list, not investigated.

## 2. Measured classification

**Both categories exist — the exclusion list conflates them.** The sweep was
run with a 900s budget against the 300s budget that produced the exclusion
list, and that difference alone reclassifies at least one spec.

### 2a. MERELY SLOW — finishes, was excluded only by the 300s budget

| spec | wall | rc |
|---|---|---|
| `test/01_unit/lib/crypto/ml_dsa_65_spec.spl` | 354s | 0 |
| `test/01_unit/os/crypto/p384_spec.spl` | 381s | 0 |
| `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl` | 394s | 1 |
| `test/01_unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl` | 409s | 0 |
| `test/01_unit/lib/crypto/ml_dsa_87_kat_spec.spl` | 510s | 0 |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` | 520s | 1 |
| `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl` | 726s | 0 |
| `test/01_unit/lib/crypto/slh_dsa_128s_spec.spl` | 860s | 0 |

**None of these is a hang.** All eight produce a verdict inside 900s and
were excluded only because they exceed the 300s per-file budget. The six
rc=0 rows pass; the two rc=1 rows (`simple_web_window_renderer`,
`simple_web_renderer`) complete with genuine test failures and should be
triaged as failures, not as hangs.

Verified from the log rather than the exit code alone — e.g.
`browser_session_fetch_wasm_chain_spec`: `SPEC FILE VERDICT: ... outcome=OK
declared>=250 executed=250 passed=250 failed=0 skipped=0 dropped=0`.

Note that `slh_dsa_128s` at 860s clears the budget by only 40s, and these
timings were taken with 4 specs running concurrently. On a quieter box more
of §2b may finish; on a busier one this spec will flip to a timeout. The
24/8/8 split is therefore a boundary, not a constant. It belongs in a performance
bucket, not a hang list. Its cost is consistent with root cause C below (the
whole JS engine running interpreted).

### 2b. TIMEOUT — no completed verdict within 900s (rc=124)

| spec | wall | rc |
|---|---|---|
| `test/01_unit/app/office/sheets/access_controller_spec.spl` | 900s | 124 |
| `test/01_unit/app/stats/doc_integration_spec.spl` | 900s | 124 |
| `test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl` | 900s | 124 |
| `test/01_unit/compiler/driver_provider_v1_spec.spl` | 900s | 124 |
| `test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/js_timer_drain_limit_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/search/unicode_17_0_0_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/web/browser_session_security_boundary_spec.spl` | 900s | 124 |
| `test/01_unit/lib/common/web/browser_session_storage_spec.spl` | 900s | 124 |
| `test/01_unit/lib/crypto/ecc_p384_p521_kat_spec.spl` | 900s | 124 |
| `test/01_unit/lib/crypto/ed448_rfc8032_kat_spec.spl` | 900s | 124 |
| `test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` | 900s | 124 |
| `test/01_unit/lib/crypto/slh_dsa_192s_256s_spec.spl` | 900s | 124 |
| `test/01_unit/lib/fs_driver/fat32_format_spec.spl` | 900s | 124 |
| `test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` | 900s | 124 |
| `test/01_unit/os/crypto/bip39_kat_spec.spl` | 900s | 124 |
| `test/01_unit/os/crypto/scram_sha256_rfc5802_spec.spl` | 900s | 124 |
| `test/01_unit/os/crypto/scram_sha512_spec.spl` | 900s | 124 |
| `test/01_unit/os/qemu_systest_contract_spec.spl` | 900s | 124 |
| `test/01_unit/os/tools/shell/text_tool_artifact_contract_spec.spl` | 900s | 124 |
| `test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl` | 900s | 124 |

**The stall is in the FIRST test, not at import.** The runner streams
per-test results as it goes — it does not buffer them — which the 2a
finisher proves: its log is 957 lines and its first `✓` line appears at
line **250**, after ~249 lines of module-load preamble. Every 2b log is
**exactly 247 lines with zero `✓` lines**. So these specs finish module
loading and then stall in (or immediately before) their first test case;
they are not import-time hangs, and they are not stalling deep in a long
run after many passing tests.

That the preamble length is identical across specs as unrelated as a
compiler parser spec, a Unicode search spec, a font-renderer spec and the JS
timer specs is a property of the shared preamble, not evidence of a shared
root cause — the preamble is the same ~247 lines of `[gc-warning]` /
`[use-warning]` module-load noise for every spec in the suite.

### 2c. FAST FAILURE — not hangs at all, they die in seconds

Eight specs terminate in **6-16 seconds** with rc=5. They never hang; they
fail at module load or lose their child process. They appear to have been
binned as hangs because they produce no test verdict, not because they ran
long.

| spec | wall | rc |
|---|---|---|
| `test/01_unit/os/drivers/input/virtio_input_mmio_contract_spec.spl` | 6s | 5 |
| `test/01_unit/os/drivers/audio/hda_controller_spec.spl` | 7s | 5 |
| `test/01_unit/os/drivers/framebuffer/fb_driver_spec.spl` | 7s | 5 |
| `test/01_unit/os/services/audio/virtio_snd_service_contract_spec.spl` | 7s | 5 |
| `test/01_unit/os/kernel/boot/mmio_test_backend_spec.spl` | 9s | 5 |
| `test/01_unit/os/kernel/timer_test.spl` | 11s | 5 |
| `test/01_unit/lib/nogc_sync_mut/concurrent/with_lock_guard_spec.spl` | 13s | 5 |
| `test/01_unit/os/arm64_desktop_arch_facade_spec.spl` | 16s | 5 |

Two distinct causes are visible in their logs:

- **Module parse/semantic failure.** `os/kernel/timer_test.spl`:
  `semantic: variable 'TscCalSource' not found`, and
  `Failed to parse module path="src/os/kernel/arch/riscv32/cpu.spl"
  error=Unexpected token: expected identifier, found FString([Literal("memory")])`.
  A riscv32 `cpu.spl` that does not parse is a real defect independent of
  any of these specs.
- **Child spawn/reap failure.** `os/drivers/framebuffer/fb_driver_spec.spl`:
  `error: test-runner: TERMINATED: child produced no exit status -- spawn or
  reap failure at the process layer, not a timeout and not a signal death`,
  verdict `executed=0 passed=0 failed=1 dropped=1 unrun=1
  reason=child-died-by-signal`.

These need triage as ordinary failures, not as performance work.

### 2d. Summary of the 40 real specs

| category | count |
|---|---|
| True hang — 900s timeout, no verdict (2b) | **24** |
| Slow but completing, 354-860s (2a) | **8** |
| Fast failure, 6-16s, rc=5 (2c) | **8** |

Of the 40 real specs, 24 produce a 900s timeout without a completed verdict.
That is a bounded measurement, not proof of a permanent hang. Sixteen — 40%
of the real population — are definitively something else: 8 complete inside
the 900s budget and were excluded only by the 300s one, and 8 fail in seconds.
Any future sweep should retain this distinction.

The whole population is now measured; there are no unmeasured rows left.

## 3. Root cause A — `set_object_property` is O(total properties) per write

`completed_animation_handle_capacity_spec` and `js_timer_drain_limit_spec`
fill the JS timer queue to `JS_TIMER_TASK_LIMIT` (**4096**) via a script
loop. With node-compat on, every `setTimeout` calls `create_object()` once
and `set_object_property()` about 25 times, so the run performs ~100,000
property writes.

`set_object_property` (`src/lib/nogc_sync_mut/js/engine/interpreter_object.spl`)
finds an existing property by scanning the **entire** flat property table
backwards — all objects' properties, not just `obj_id`'s:

```
var existing_i = prop_keys.len() - 1
while existing_i >= 0:
    if prop_obj_ids[existing_i] == obj_id and prop_keys[existing_i] == key:
```

At ~100,000 total entries that is O(total) per write and O(total²) for the
run. **This is the spec-level blocker and it is NOT fixed.** Closing it needs
an `obj_id`-keyed index (or per-object property lists) in `ObjectStore` —
a design change, deliberately not attempted here.

## 4. Root cause B — COW alias removed in one family (partial optimization)

Layered on top of the scan, the same function took seven aliases out of
`self.object_store` and stored all seven back:

```
var object_store = self.object_store
var prop_obj_ids: [i64] = object_store.prop_obj_ids
... 5 more ...
object_store.prop_obj_ids = prop_obj_ids
self.object_store = object_store
```

Under Simple's copy-on-write value semantics each alias-mutate-store-back
deep-copies a whole parallel array, so every property write copied seven
arrays of length = total property count. `create_object()` had the same shape
and deep-copied the **entire object store** per object creation.

The alias round trip is removed from the `nogc_sync_mut` family by mutating
through the single owner (`self.object_store.<field>`), per
`.claude/rules/code-style.md`. A bounded semantic regression covers object-id
allocation plus property insert, isolation, and update behavior. Historical
64-timer evidence still yields `pending=64`, rc=0; its 41s→44s wall time is
noise, not evidence of a speedup. The surviving O(n²) scan of §3 still governs
at n=4096, so no timer timeout or hang is claimed resolved.

**The same defect is still present in the other two stdlib families** and is
deliberately left for a change that can validate them:
- `src/lib/nogc_async_mut/js/engine/interpreter_object.spl`
- `src/lib/gc_async_mut/js/engine/interpreter_object.spl` (used by the
  `browser_session_*` specs)

## 5. Root cause C — one bad line disables JIT for the whole JS interpreter

`_filter_request_headers` ends with a statement referencing `value`, which is
**not a parameter of the function** and is not otherwise bound:

```
me _filter_request_headers(headers_text: text) -> text:
    ...
    kept.join("\n")
    js_to_string(value)      # <-- undefined variable, after the real result
```

Present identically in all three families:
- `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl:587`
- `src/lib/nogc_async_mut/js/engine/interpreter_async.spl:422`
- `src/lib/gc_async_mut/js/engine/interpreter_async.spl:508`

Because it is the trailing expression it is also the implicit return, so the
function does not return the filtered headers it computed — a latent
correctness bug in cookie stripping.

Its immediate effect is worse: codegen fails on it, and the failure is not
contained to the function. Observed on every JS-engine run:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
compile: Module error: codegen: 1 function body/bodies failed to compile:
[JsInterpreter._filter_request_headers]
```

One function takes the **whole module** down to the interpreter, so the
entire JS engine runs interpreted. This is plausibly the dominant cost for
the whole JS/browser spec cluster.

**Removing the line is not yet safe — do not "just delete it".** Deleting it
in all three families was tried and A/B-tested against the same binary:

| tree | n=8 script | result |
|---|---|---|
| `origin/main` | 32s | rc=0, `pending=8` |
| line deleted | 485s | **rc=134, stack overflow** |
| line restored | 32s | rc=0, `pending=8` |

With the line gone the module JIT-compiles, the engine reports
`[engine-demotion] reason=hybrid-interp-splice`, and the run aborts with
`thread 'simple-main' has overflowed its stack`. So there is a second, latent
defect in the JIT / hybrid-interp-splice path for this module that the
codegen failure has been masking. The captured abort log is retained at
`evidence/unit_spec_hangs_42_excluded_2026-08-27/fx_jitfix_8.log` (SHA-256
`0e387ff34738d5ea5d510c8e7e94835529c556df6fe0569b9b5e3c28a89efbb7`).

Fixing this pair (the dangling line **and** the stack overflow it exposes) is
the highest-value remaining work for the JS cluster.

## 6. Root cause D — `pbkdf2_native_perf_spec` has no native acceleration

The spec name asserts a native path. `_pbkdf2_block_sha*`
(`src/lib/common/crypto/pbkdf2.spl:91-142`) calls `hmac_sha*_bytes(password,
u)` once per iteration with a **constant** password, and each call rebuilds
the ikey/okey pads from scratch (`src/lib/common/crypto/hmac.spl:34-56`,
`:236-256`). Hoisting the pads is a real but modest win (~15% by inspection:
the pads are ~128-256 ops against ~1280 for the two SHA-256 compressions),
so it will not on its own bring a 900s timeout under budget. Classify as
**needs native acceleration**, not as a COW defect. The pad hoist is still
worth doing separately; it is not done here because shipping it would imply
the spec was addressed.

## 7. Root cause E — `rsa_pss` modular reduction is O(n²)

`_pss_bi_mod` (`src/os/crypto/rsa_pss.spl:164-198`) reduces by repeated
subtraction, rebuilding two full limb arrays per bit of the operand (~4096
iterations), and `_pss_bi_mod_exp` (`:200`) calls it ~4096 times. This is the
`rsa_pss_sha256_roundtrip_slow_spec` blocker. The fix is Barrett or
Montgomery reduction — real crypto work, deliberately not rushed here.

## 8. Why this class was invisible to the ratchet

`scripts/check/check-cow-alias-hotpath.shs` reports
`FAIL — 9803 file(s) scanned, 958 offender(s), 196 new, 181 stale`, and **not
one finding touches any of the code above**. Two independent gaps:

1. **Scope.** The guard scans only `src/compiler` and `src/lib` (script lines
   402-403). `src/os/**` is entirely unscanned — and that is where the
   crypto for 12 of these specs lives (`src/os/crypto/*`).
2. **Shape.** Its ROUNDTRIP rule pairs `val t = self.f` with `t.push(...)` or
   `t[i] = ...`. The shape in §4 mutates a *field of* the alias
   (`object_store.prop_values = prop_values`, `object_store.next_id = ...`),
   which the rule does not match. So the single most expensive instance of
   this defect class in the tree was never flagged.

Both gaps should be closed before the baseline is trusted as a description of
the tree.
