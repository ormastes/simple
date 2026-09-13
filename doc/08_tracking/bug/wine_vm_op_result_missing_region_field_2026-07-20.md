# Bug: `WineVmOpResult` is missing a `region` field that both src and test callers depend on

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Date: 2026-07-20

## Symptom

`test/01_unit/lib/common/wine_dll_file_view_spec.spl`:
```
wine dll file view
  ✗ maps a validated DLL file probe into a persistent process image view
    semantic: class `WineVmOpResult` has no field named `region`
  ✗ maps a retained DLL file view only after PEB/TEB VM byte-write readback
    semantic: class `WineVmOpResult` has no field named `region`
  ✗ rejects invalid probe or mapping inputs
    semantic: function expects 4 argument(s), but more were provided

3 examples, 3 failures
```

Command:
```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/common/wine_dll_file_view_spec.spl --no-session-daemon
```

## Root cause

`src/lib/common/wine_vm_adapter.spl:22-25` defines:
```
class WineVmOpResult:
    ok: bool
    state: text
    space: WineVmSpace
```
No `region` field, and `wine_vm_commit` takes 4 positional args
(`space, address, size, protection`) — see `wine_vm_adapter.spl:45`.

But **production src** `src/lib/common/wine_dll_file_view.spl:48` reads
`mapped.region.base` / `mapped.region.size` off a `WineVmOpResult`-shaped
value:
```
_result(true, "", probe.dll_name, probe.selected_path, mapped.region.base, mapped.region.size, probe.entrypoint_rva, mapped.space, evidence, "dll-file-backed-view-mapped")
```

And the spec's own test helper `_commit_fixed` (test file lines 43-48) does
the same plus calls `wine_vm_commit` with only 3 args instead of 4:
```
fn _commit_fixed(space: WineVmSpace, base: i64, size: i64, perms: text) -> WineVmSpace:
    val reserved = wine_vm_reserve_fixed(space, base, size)
    if not reserved.ok:
        return reserved.space
    val committed = wine_vm_commit(reserved.space, reserved.region.base, perms)  # missing `size` arg, `.region` doesn't exist
    committed.space
```

Additionally `wine_vm_space_find(space, address)` (`wine_vm_adapter.spl:19-20`)
returns a plain `bool` (`space.ok and address >= 0`), but the spec's first
`it` block treats the result as a struct with `.kind`/`.perms` fields:
```
val region = wine_vm_space_find(result.space, 0x79000000)
expect(region.kind).to_equal("image")
expect(region.perms).to_equal("rx")
```

## Why this is NOT a stale-test fix

`wine_vm_adapter.spl` is a stub: `WineVmOpResult` carries no region/committed
state at all (no base/size/perms tracking), so `wine_vm_space_find` can never
distinguish region kind/perms, and there is no `region` value anywhere to read
`.base`/`.size` from. Editing only the test cannot make it pass — the
production call site `wine_dll_file_view.spl:48` independently references the
same nonexistent `.region` field, so `wine_dll_map_file_backed_view` (called
by all 3 `it` blocks) is broken at the source level regardless of how the spec
calls it. A real fix requires adding actual region/permission tracking to
`WineVmOpResult`/`WineVmSpace` in `wine_vm_adapter.spl` — out of scope for a
test-only shard fix.

## Affected

- `test/01_unit/lib/common/wine_dll_file_view_spec.spl` (all 3 examples)
- Production src: `src/lib/common/wine_dll_file_view.spl:48` (same `.region` reference, latent breakage)

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
