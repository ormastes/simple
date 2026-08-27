# 42 unit specs excluded from the `test/01_unit` sweep as hangs (2026-08-27)

Status: OPEN. Diagnosis complete for the JS/browser cluster; one mechanical
fix landed; the spec-level blockers are recorded below and are NOT closed.

Binary under test (identical for every measurement in this record):
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

Every real spec measured so far is a **pure timeout** — no verdict within
900s, rc=124. None finished slowly; there is so far no "merely slow"
category in this population.

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

The remaining specs from the list were still being measured when this record
was written; the sweep writes to `/mnt/data/tmp/claude-1000/hang_out/times.tsv`.
Their measured rows must be appended here before this record is closed.

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

## 4. Root cause B (FIXED) — COW alias deep-copy in the same function

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

Fixed by mutating through the single owner (`self.object_store.<field>`), per
`.claude/rules/code-style.md`. Correctness re-verified (a 64-timer script
still yields `pending=64`, rc=0); wall time at n=64 is unchanged at 41s→44s
because that size is dominated by ~28s of fixed startup, and the surviving
O(n²) scan of §3 still governs at n=4096.

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
codegen failure has been masking. Evidence log:
`/mnt/data/tmp/claude-1000/hang_out/fx_jitfix_8.log`.

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
