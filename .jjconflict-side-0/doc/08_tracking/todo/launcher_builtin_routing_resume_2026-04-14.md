# Launcher Exec Path → builtin_binary_registry Routing — Diagnosis Resume
Date: 2026-04-14
Agent: LR (Launcher Routing Diagnosis)

---

## 1. Current Exec Flow (shortcut press → -38)

```
desktop_e2e_entry.spl
  └─ launcher_shortcut_dispatch(KEY_H/F/T, MOD_META)        # launcher.spl:505
       ├─ [loop] _app_key(i) == key? → launcher_launch(name) # registry lookup
       │      └─ posix_spawn(path, APP_PRIORITY)             # launcher.spl:432
       │             └─ baremetal_stubs.c posix_spawn stub
       │                    → returns -38 (ENOSYS)           # stub not wired
       └─ [fallback] _dispatch_seeded_shortcut(key, mods)    # launcher.spl:485
              └─ _launch_seeded_app(slot, name, path, …)     # launcher.spl:456
                     └─ posix_spawn(path, APP_PRIORITY)      # SAME stub → -38
```

Both the registry path and the seeded fallback converge on `posix_spawn`, which
returns `-38 ENOSYS` on baremetal because the stub in `baremetal_stubs.c`
(`examples/simple_os/arch/x86_64/boot/baremetal_stubs.c:3598`) has no wired
exec implementation. `hello_world`, `file_manager`, and `shell` follow this
path and thus always return `-38`.

---

## 2. Browser Demo's Special Path — Why It Succeeds

Browser Demo succeeds via a **test-harness local-fallback** in
`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`, NOT through the
launcher at all:

```
desktop_e2e_entry.spl
  └─ val dispatched = launcher_shortcut_dispatch(KEY_B, META_MODIFIER)
     if not dispatched:
         _launch_browser_demo_local(shell)    ← direct in-process call
         browser_local_fallback = true
         serial_println("shortcut:ok … mode=local-fallback")
```

`_launch_browser_demo_local` calls `browser_demo_remote_main()` directly
(or via the shell object) without going through `posix_spawn`. This bypasses
the baremetal exec stub entirely. The `shortcut:ok mode=local-fallback` log
confirms this path.

**No equivalent local-fallback exists for `hello_world`, `file_manager`, or
`shell`.** When their shortcuts fail the registry/seeded dispatch, the
`desktop_e2e_entry` code has no `_launch_*_local` fallback — it just observes
the `-38` return and the test considers it `shortcut:fail`.

---

## 3. Why builtin_binary_registry Doesn't Help (Yet)

`builtin_binary_registry.spl` (`resolve_builtin_binary`) maps paths like
`/sys/apps/hello_world` → `hello_world_remote_main` function pointer. This
registry IS consulted by the **kernel syscall handler** (`syscall.spl:571`)
for the `SYS_SPAWN_BINARY` (id=13) syscall path.

However, `launcher_launch` in `launcher.spl:432` calls **`posix_spawn`**, not
`SYS_SPAWN_BINARY`. `posix_spawn` goes through the POSIX compat layer
(`os.posix.process_compat`), which calls a different syscall that hits the
baremetal `-38` stub — it never reaches `resolve_builtin_binary`.

Additionally, there IS a `spawn` import at `launcher.spl:25`
(`os.userlib.process.{spawn}`) and prior session diffs show a version of
`launcher_launch` that uses:

```spl
val pid_result = if val Some(entry) = _builtin_remote_app_entry(path):
    match spawn(entry, APP_PRIORITY): ...
else:
    posix_spawn(path, APP_PRIORITY)
```

But the **current live file** (`launcher.spl:432`) does NOT have this check —
it calls `posix_spawn` directly. The `_builtin_remote_app_entry` helper exists
in launcher.spl (mapping `/sys/apps/hello_world` and `/sys/apps/browser_demo`)
but is **not called from `launcher_launch`**.

---

## 4. Proposed Fix

### Fix Site
**File:** `src/os/services/launcher/launcher.spl`  
**Function:** `launcher_launch` (line 417)

### Edit Required
Replace the direct `posix_spawn` call with a `_builtin_remote_app_entry`
check-first pattern:

```spl
fn launcher_launch(name: text) -> i64:
    val idx = _app_index_by_name(name)
    if idx < 0:
        serial_println("[launcher] App not found: {name}")
        return -1

    serial_println("[launcher] Launching: {name}")
    val slot = idx.to_u64()
    val path = app_path[slot]
    val pid_result = if val Some(entry) = _builtin_remote_app_entry(path):
        match spawn(entry, APP_PRIORITY):
            case Ok(pid): pid.to_i64()
            case Err(_): -1
    else:
        posix_spawn(path, APP_PRIORITY)
    if pid_result < 0:
        app_launch_state[slot] = "failed"
        app_exit_code[slot] = pid_result.to_i32()
        serial_println("[launcher] Failed to launch {name}: {pid_result}")
        return pid_result
    _finalize_launch(slot, name, pid_result.to_u64())
```

Also apply the same pattern to `_launch_seeded_app` (line 456) which also
calls `posix_spawn` directly.

### Also Required
`_builtin_remote_app_entry` currently only maps `hello_world` and
`browser_demo`. To cover `file_manager` and `shell` (whose `remote_main`
functions HW added to `builtin_binary_registry.spl`), the function must
be extended — but since the launcher already imports only
`hello_world_remote_main` and `browser_demo_remote_main` at lines 26-27,
it also needs:

```spl
use os.apps.file_manager.file_manager.{file_manager_remote_main}
use os.apps.shell.shell_app.{shell_remote_main}
```

And add cases in `_builtin_remote_app_entry`:
```spl
case "/sys/apps/file_manager":
    Some(file_manager_remote_main as u64)
case "/sys/apps/shell":
    Some(shell_remote_main as u64)
```

---

## 5. Why This Requires launcher.spl Edit (SF Territory)

The fix is entirely within `src/os/services/launcher/launcher.spl`:
- `launcher_launch` must call `_builtin_remote_app_entry` before `posix_spawn`
- `_launch_seeded_app` must do the same
- New imports for `file_manager_remote_main` and `shell_remote_main`
- Extended `_builtin_remote_app_entry` match arms

This file is marked **SF (Special Files) territory** — it requires SF agent
or explicit owner approval to modify.

**Alternative (no launcher.spl touch):** Add per-app local-fallback functions
in `desktop_e2e_entry.spl` (same approach as `_launch_browser_demo_local`).
This is a test-harness workaround rather than a real fix, but it would unblock
`hello_world` / `file_manager` / `shell` shortcut tests without touching
launcher.spl. The downside is it only fixes the E2E test path, not real
keyboard-driven launches on baremetal.

---

## 6. Blocker Category

**Requires SF reopen.** The real fix is a 4-line change inside
`launcher_launch` in `src/os/services/launcher/launcher.spl`. An agent CAN
land this once SF territory is unlocked, as there is no architectural
uncertainty — the `spawn` import and `_builtin_remote_app_entry` helper are
already present; `launcher_launch` just needs to use them.

The test-harness workaround (local-fallback in `desktop_e2e_entry.spl`) does
NOT require SF and could be landed immediately by any agent.

---

## 7. Files Referenced

| File | Role |
|------|------|
| `src/os/services/launcher/launcher.spl` | Fix site — `launcher_launch` + `_launch_seeded_app` + `_builtin_remote_app_entry` |
| `src/os/kernel/loader/builtin_binary_registry.spl` | Has `file_manager_remote_main` + `shell_remote_main` (HW's additions) |
| `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` | Browser Demo local-fallback lives here |
| `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` | `posix_spawn` stub returns `-38` (line ~3598) |
| `src/os/kernel/ipc/syscall.spl` | `resolve_builtin_binary` consulted at line 571 (SYS_SPAWN_BINARY path only) |
