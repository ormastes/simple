# RESOLVED: tree-wide `native-build` death — the native-noop invocation frame framed a raw i64 `mcdc_mode`

- **Status:** RESOLVED 2026-09-13
- **Introduced:** `e0fa5ef45e2` (2026-09-07, "WIP: harmonize bootstrap references
  and migrate kernel plugins (#319)") — the same commit added both the bare
  `aspect.mcdc_mode,` element and `driver_native_noop_request_v1` on the default
  native-build path, so the defect was reachable from the moment it landed.
- **Fixed in:** this change — `aspect.mcdc_mode.to_text()` in
  `src/compiler/80.driver/cache/native_noop_admission.spl:57`.
- **Regression pin:** `test/01_unit/compiler/driver/native_noop_invocation_identity_spec.spl`

## Symptom

Every `native-build` on the tree died before compiling any user logic:

```
error: semantic: method `len` not found on type `i64` (receiver value: 0)
error: native-build worker exited with code 1.
```

It reproduced on a three-line hello world that contains no `.len()` anywhere:

```
fn main():
    println("hello")
```

`compile` on the same file succeeded (exit 0). Only `native-build` was affected.

## Root cause

`native_noop_normalized_invocation_v1`
(`src/compiler/80.driver/cache/native_noop_admission.spl:31`) builds a `[text]`
literal of ~45 option fields and passes it to `native_noop_frame_v1`, which does
`value.len()` on **every** element:

```
fn native_noop_frame_v1(values: [text]) -> text:
    var framed = "{values.len()};"
    for value in values:
        framed = framed + "{value.len()}:{value}"
```

Every non-text field in that literal is converted with `.to_text()` — except
`aspect.mcdc_mode`, which was passed bare. It is
`AspectParamsV1.mcdc_mode: i64` (`src/lib/common/plugin/aspect_params.spl:19`,
default `0`), **not** a text. The raw i64 reached the frame loop and
`value.len()` raised. Its immediate neighbours `aspect.compile_log_level` and
`aspect.runtime_log_level` are the same i64 shape and already had `.to_text()`;
this was a single field that lost the treatment.

`driver_native_noop_request_v1` (`driver_orchestration.spl:68`) runs on the
DEFAULT native-build path, before any user logic — hence "tree-wide, before the
program's own source is considered".

## Why it took so long to localize

The diagnostic carries **no source location and no stack**, so it read as a
stdlib erased-receiver/typing regression and drew several investigations toward
recently-landed compiler PRs. Three things made it worse:

1. The `(receiver value: 0)` shape is identical to the known
   unregistered-extern-returns-nil class
   (`unregistered_extern_silent_nil_2026-08-01.md`), which is a red herring here.
2. An unrelated `SCV-E-SNAPSHOT: snapshot-inventory-unavailable` line printed
   immediately before it, suggesting the SCV freeze was the cause. It is not —
   the error reproduces identically with `SIMPLE_SCV_FREEZE_FALLBACK=1`.
3. The seed binary in use predated the day's PRs, so those PRs could not have
   been the cause, but nothing said so.

**The tool that actually solved it** (one 90 s run, after several hours of
bisecting the wrong axis) is the interpreter's own method-not-found stack:

```
SIMPLE_INTERP_OOB_DEBUG=1 SIMPLE_DEBUG_FIELD_ACCESS=1 <seed> native-build ...
```

which printed the exact `.spl` frame chain:

```
main -> cli_native_build_with_environment_variant_policy_v1 -> _cli_native_build
  -> compiler_driver_run_compile -> compile
  -> compile_with_reverse_reference_owner_v1 -> driver_native_noop_request_v1
  -> native_noop_normalized_invocation_v1 -> native_noop_frame_v1
```

Reach for that pair first on any locationless `method not found` raised inside
self-hosted compiler code.

## A bisect note, recorded because it cost real time

A `git bisect` pinning the seed binary while moving the tree is **not sound**
here and produced two false results before being abandoned:

- the first probe program used `fun main()` instead of `fn main()`, so the
  "good" endpoint was really "failed earlier, for a different reason";
- even with a valid program, a Sep-12 seed over a Sep-5 tree is a pairing that
  never existed, and the 09-05 endpoint failed with a *different* error. A probe
  that tests for the ABSENCE of one error string scores every unrelated failure
  as GOOD.

Introduction was found with `git log --reverse -S'aspect.mcdc_mode,'` instead —
note `git log -1 -S` gives the *latest* change, not the introduction.

## Not fixed here — `native-build` of hello is still red

Removing this defect uncovers two further, independent blockers on the same
path. Both are beyond this change's scope and are stated rather than implied:

1. `error: persistent package index admission failed: scv-authority-missing`.
   Already filed as
   `stage3_step_omits_package_index_cold_init_scv_authority_missing_2026-09-13.md`.
   Worked around for diagnosis with `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`.
2. With that set, the build reaches `aop_weave` and then fails with
   `error: semantic: function expects argument for parameter 'msg', but none was
   provided`. `SIMPLE_DEBUG_ARG_BINDING=1` prints
   `missing param 'msg'; full param list=["scope", "msg"]; args given=1` — a
   one-argument call resolving to one of `src/lib/log.spl`'s two-argument
   `fatal/error/warn/info/debug(scope, msg)` helpers. This has the shape of the
   `compiler_cross_module_private_symbol_collision` class the build already warns
   about in bulk on this path. **Filed separately; not diagnosed further here.**

So this record closes the `len`-on-i64 defect specifically. It does **not**
claim `native-build` is green.

## Landing note — test-tree divergence step-over (required record)

`check-test-tree-divergence.shs` is RED on `origin/main` independently of this
change: `FAIL — 3941 diverged vs 965 baselined (3079 new, 103
fixed-but-still-baselined); 32 mirror-only (31 unallowlisted)`. Per
`.claude/rules/vcs.md`, the mechanical escape was used and its result is
recorded here rather than stepped over silently:

```
check-test-tree-divergence-delta.shs b071470d429 87e10fb0b28
  -> PASS — 3213 pre-existing offender(s), 0 introduced by this range
```

Offender list saved by the helper to
`$TMPDIR/test_tree_divergence_preexisting.txt` (3,941 lines, first rows
`integration:app/add_remove_log_modes_spec.spl`,
`integration:app/app_mcp_intensive_spec.spl`,
`integration:app/brief_log_modes_spec.spl`).

Mirror pairs touched by this range, enumerated rather than assumed
(`git diff --name-only b071470d429..87e10fb0b28 -- test/01_unit test/unit
test/02_integration test/integration`):

- `test/01_unit/compiler/driver/native_noop_invocation_identity_spec.spl` — new
  file, no twin under `test/unit/`, so no pair is made non-identical by it.

Other pre-push guards, all run in the foreground with exit codes captured:
conflict-markers PASS (5 files), conflict-tree PASS (2 commits), tree-size PASS
(base 137,237 files), runtime-api-regression PASS (3,223 symbols, 0 removed),
no-revert PASS (5 files), rt-dual-implementation PASS (2,508 symbols, 0 new/0
stale), c-runtime-compiles PASS (147 files, 0 errors, 6 external-SDK skips).
