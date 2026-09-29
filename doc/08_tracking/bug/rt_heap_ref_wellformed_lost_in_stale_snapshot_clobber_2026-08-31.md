# `rt_heap_ref_wellformed` was landed, then lost to the 08-26 stale-snapshot clobber — docs survived, code did not

- **Filed:** 2026-08-31
- **Status:** OPEN — restoration in progress
- **Severity:** a shipped fix is absent from `main` while the tree still documents it as present
- **Causes:** `stage2_positional_entry_segv_module_surfaces_null_2026-08-31.md`

## Summary

`57271d9ba49` (2026-08-23) landed a runtime formation probe and fail-closed HIR
guards across 9 code files. `4edef8fab8e` (2026-08-26, "feat: snapshot current
development state") — the stale-snapshot clobber already known to this repo —
removed the implementation. PR #41 (`17f145748c1`, "restore 112 files lost in
stale-snapshot 4edef8fab8e") recovered 112 files but **did not touch
`src/runtime/runtime_native.c`**, so this fix was not among them.

Both commits are ancestors of `main`. The fix is absent from `main` today.

## Measured

`grep -c heap_ref_wellformed` on `src/runtime/runtime_native.c`:

| revision | lines | occurrences |
|---|---|---|
| `57271d9ba49` (the fix) | 11,982 | 1 |
| `4edef8fab8e` (the clobber) | 12,290 | **0** |
| `origin/main` today | 13,166 | **0** |

The file GREW across the clobber. A file-count or size guard cannot see this:
the tree is structurally healthy and the file is bigger than before. Only the
symbol is gone. This is precisely the gap
`check-runtime-api-regression-push.shs` exists for, and it did not fire because
the removal predates that guard's coverage of this path and the symbol is not
an `rt_*` export it tracks in the same way.

## The state that makes this dangerous

**The documentation survived; the implementation did not.**

| file | mentions on main |
|---|---|
| `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` | 9 |
| `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` | 4 |
| all 9 implementation files | **0** |

So the hardening plan reads as delivered, and a reader checking "is this done?"
by consulting the plan gets the wrong answer. The two regression specs written
specifically to fence this defect
(`test/01_unit/runtime/heap_ref_wellformed_probe_spec.spl`,
`hir_entry_payload_formation_guard_spec.spl`) were lost with it, so nothing
failed when it disappeared.

## Files that lost the implementation

```
src/compiler/80.driver/driver_hir_pipeline_lowering.spl
src/compiler_rust/common/src/runtime_symbols.rs
src/compiler_rust/runtime/src/value/mod.rs
src/compiler_rust/runtime/src/value/objects.rs
src/runtime/runtime.h
src/runtime/runtime_native.c
src/runtime/simple_core/core_enum.spl
src/runtime/test/rt_heap_ref_wellformed_selfcheck.c
test/01_unit/runtime/heap_ref_wellformed_probe_spec.spl
test/01_unit/compiler/hir_entry_payload_formation_guard_spec.spl
```

## Why it matters right now

The defect class it guards is, in its own words: *"a Some/Ok-tagged enum whose
PAYLOAD WORD is 0 passes every guard the runtime has, then SIGSEGVs on the first
field load at address 0."* Nothing else catches it — `rt_enum_payload` returns a
0 payload verbatim, `rt_is_some` tests only the discriminant, `rt_unwrap_or_trap`
gates on the discriminant, and a `== nil` guard cannot fire because a zeroed
payload is not the nil representation.

That is exactly the Stage-2 crash filed today: a first-field load at `0x8` off a
zero base. The upstream commit that added the now-failing positional probe
(`22ab5ea482a`) explicitly assumed this fix was present at origin — *"Underlying
compiler defect is already fixed at origin"* — and it is not.

## Restoration caveat, stated so it is not overclaimed

By its own commit message this is a **hardening guard**, not a repair of the
underlying payload-zero bug: *"with no claim that it repairs the Linux stage
binaries."* Restoring it should convert the SEGV into a clean named error
(`E-DRIVER-HIR-OWNER-MALFORMED` / `E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED`).

Whether that makes Stage-2 admission pass is a MEASUREMENT, not an assumption.
It may: `22ab5ea482a` records that *"arm 2 is a NO-CRASH check (a healthy
compiler may reject a positional entry with a clean rc=1)"*. Do not record the
gate as passing without running it.

Restoration must apply the ADDITIONS only. `runtime_native.c` has grown from
11,982 to 13,166 lines since the fix; restoring whole files from `57271d9ba49`
would itself be a clobber.

## Follow-up worth doing separately

PR #41's restore was incomplete and nothing detected that. A re-audit of
`4edef8fab8e` against its parent — symbol-level, not file-level, since the file
COUNT was never the signal here — would show whether anything else is still
missing.
