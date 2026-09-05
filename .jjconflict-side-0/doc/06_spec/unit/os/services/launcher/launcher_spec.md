# @manual: primary

> Purpose: Prove that Launcher registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Launcher registry.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/services/launcher/launcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Launcher registry.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-SERVICES-001
doc/01_research/local/REQ-OS-SERVICES-001.md
doc/03_plan/sys_test/REQ-OS-SERVICES-001.md
doc/04_architecture/REQ-OS-SERVICES-001.md
doc/05_design/REQ-OS-SERVICES-001.md

## Scenarios

### Launcher registry

#### seeds built-in apps with manifest-backed binary identities

- Verify: seeds built-in apps with manifest-backed binary identities
   - Expected: launcher_get_app_count() equals `15`
   - Expected: launcher_get_app_name(0) equals `Hello World`
   - Expected: launcher_get_app_path(0) equals `/sys/apps/hello_world.smf`
   - Expected: launcher_get_app_identity(0) equals `/sys/apps/hello_world`
   - Expected: launcher_get_app_name(1) equals `Calculator`
   - Expected: launcher_get_app_path(1) equals `/sys/apps/calculator.smf`
   - Expected: launcher_get_app_name(2) equals `Clock`
   - Expected: launcher_get_app_path(2) equals `/sys/apps/clock.smf`
   - Expected: launcher_get_app_name(3) equals `File Manager`
   - Expected: launcher_get_app_path(3) equals `/sys/apps/file_manager.smf`
   - Expected: launcher_get_app_name(4) equals `Terminal`
   - Expected: launcher_get_app_path(4) equals `/sys/apps/shell.smf`
   - Expected: launcher_get_app_name(5) equals `Browser Demo`
   - Expected: launcher_get_app_path(5) equals `/sys/apps/browser_demo.smf`
   - Expected: launcher_get_app_name(6) equals `Editor`
   - Expected: launcher_get_app_path(6) equals `/sys/apps/editor.smf`
   - Expected: launcher_get_app_name(7) equals `Simple Browser`
   - Expected: launcher_get_app_path(7) equals `/sys/apps/simple_browser.smf`
   - Expected: launcher_get_app_name(8) equals `Simple Compiler`
   - Expected: launcher_get_app_path(8) equals `/sys/apps/simple_compiler.smf`
   - Expected: launcher_get_app_name(9) equals `Simple Interpreter`
   - Expected: launcher_get_app_path(9) equals `/sys/apps/simple_interpreter.smf`
   - Expected: launcher_get_app_name(10) equals `Simple Loader`
   - Expected: launcher_get_app_path(10) equals `/sys/apps/simple_loader.smf`
   - Expected: launcher_get_app_name(11) equals `Simple`
   - Expected: launcher_get_app_path(11) equals `/sys/apps/simple.smf`
   - Expected: launcher_get_app_identity(11) equals `/sys/apps/simple`
   - Expected: launcher_get_app_name(12) equals `LLVM`
   - Expected: launcher_get_app_path(12) equals `/sys/apps/llvm.smf`
   - Expected: launcher_get_app_name(13) equals `Clang`
   - Expected: launcher_get_app_path(13) equals `/sys/apps/clang.smf`
   - Expected: launcher_get_app_name(14) equals `Rust`
   - Expected: launcher_get_app_path(14) equals `/sys/apps/rust.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: seeds built-in apps with manifest-backed binary identities")
launcher_init()
expect(launcher_get_app_count()).to_equal(15)  # oracle: 15 — named expected value from the requirement
expect(launcher_get_app_name(0)).to_equal("Hello World")
expect(launcher_get_app_path(0)).to_equal("/sys/apps/hello_world.smf")
expect(launcher_get_app_identity(0)).to_equal("/sys/apps/hello_world")
expect(launcher_get_app_name(1)).to_equal("Calculator")
expect(launcher_get_app_path(1)).to_equal("/sys/apps/calculator.smf")
expect(launcher_get_app_name(2)).to_equal("Clock")
expect(launcher_get_app_path(2)).to_equal("/sys/apps/clock.smf")
expect(launcher_get_app_name(3)).to_equal("File Manager")
expect(launcher_get_app_path(3)).to_equal("/sys/apps/file_manager.smf")
expect(launcher_get_app_name(4)).to_equal("Terminal")
expect(launcher_get_app_path(4)).to_equal("/sys/apps/shell.smf")
expect(launcher_get_app_name(5)).to_equal("Browser Demo")
expect(launcher_get_app_path(5)).to_equal("/sys/apps/browser_demo.smf")
expect(launcher_get_app_name(6)).to_equal("Editor")
expect(launcher_get_app_path(6)).to_equal("/sys/apps/editor.smf")
expect(launcher_get_app_name(7)).to_equal("Simple Browser")
expect(launcher_get_app_path(7)).to_equal("/sys/apps/simple_browser.smf")
expect(launcher_get_app_name(8)).to_equal("Simple Compiler")
expect(launcher_get_app_path(8)).to_equal("/sys/apps/simple_compiler.smf")
expect(launcher_get_app_name(9)).to_equal("Simple Interpreter")
expect(launcher_get_app_path(9)).to_equal("/sys/apps/simple_interpreter.smf")
expect(launcher_get_app_name(10)).to_equal("Simple Loader")
expect(launcher_get_app_path(10)).to_equal("/sys/apps/simple_loader.smf")
expect(launcher_get_app_name(11)).to_equal("Simple")
expect(launcher_get_app_path(11)).to_equal("/sys/apps/simple.smf")
expect(launcher_get_app_identity(11)).to_equal("/sys/apps/simple")
expect(launcher_get_app_name(12)).to_equal("LLVM")
expect(launcher_get_app_path(12)).to_equal("/sys/apps/llvm.smf")
expect(launcher_get_app_name(13)).to_equal("Clang")
expect(launcher_get_app_path(13)).to_equal("/sys/apps/clang.smf")
expect(launcher_get_app_name(14)).to_equal("Rust")
expect(launcher_get_app_path(14)).to_equal("/sys/apps/rust.smf")
```

</details>

#### registers apps with idle launch state

- Verify: registers apps with idle launch state
   - Expected: registered is true
   - Expected: launcher_get_app_count() equals `16`
   - Expected: demo_idx equals `15`
   - Expected: launcher_get_app_name(demo_slot) equals `Demo App`
   - Expected: launcher_get_app_path(demo_slot) equals `/apps/demo`
   - Expected: launcher_get_app_identity(demo_slot) equals `/apps/demo`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `idle`
   - Expected: launcher_get_app_window_count(demo_slot) equals `0`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `0`
   - Expected: launcher_get_app_launch_count(demo_slot) equals `0`
   - Expected: launcher_get_app_last_pid(demo_slot) equals `0`
   - Expected: launcher_get_app_is_headless(demo_slot) is false
   - Expected: launcher_get_running_app_count() equals `0`
   - Expected: launcher_get_process_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: registers apps with idle launch state")
launcher_init()
val registered = launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
expect(registered).to_equal(true)
expect(launcher_get_app_count()).to_equal(16)  # oracle: 16 — named expected value from the requirement
val demo_idx = launcher_find_by_name("Demo App")
expect(demo_idx).to_equal(15)  # oracle: 15 — named expected value from the requirement
val demo_slot = demo_idx.to_u64()
expect(launcher_get_app_name(demo_slot)).to_equal("Demo App")
expect(launcher_get_app_path(demo_slot)).to_equal("/apps/demo")
expect(launcher_get_app_identity(demo_slot)).to_equal("/apps/demo")
expect(launcher_get_app_launch_state(demo_slot)).to_equal("idle")
expect(launcher_get_app_window_count(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_exit_code(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_launch_count(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_last_pid(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_is_headless(demo_slot)).to_equal(false)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### maps text and image files to the default opener app

- Verify: maps text and image files to the default opener app
   - Expected: launcher_associated_app_for_path("/home/readme.txt") equals `/sys/apps/editor`
   - Expected: launcher_associated_app_for_path("/home/notes.spl") equals `/sys/apps/editor`
   - Expected: launcher_associated_app_for_path("/home/picture.png") equals `/sys/apps/image_viewer`
   - Expected: launcher_associated_app_for_path("/home/archive.bin") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: maps text and image files to the default opener app")
launcher_init()
expect(launcher_associated_app_for_path("/home/readme.txt")).to_equal("/sys/apps/editor")
expect(launcher_associated_app_for_path("/home/notes.spl")).to_equal("/sys/apps/editor")
expect(launcher_associated_app_for_path("/home/picture.png")).to_equal("/sys/apps/image_viewer")
expect(launcher_associated_app_for_path("/home/archive.bin")).to_equal("")
```

</details>

#### builds candidates for an unknown command without registering it

- Verify: builds candidates for an unknown command without registering it
   - Expected: candidates[0] equals `/sys/apps/definitely_missing_simpleos_command.smf`
   - Expected: launcher_find_by_name("definitely_missing_simpleos_command") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: builds candidates for an unknown command without registering it")
launcher_init()
val candidates = launcher_command_resolution_candidates("definitely_missing_simpleos_command", "/", "")
expect(candidates[0]).to_equal("/sys/apps/definitely_missing_simpleos_command.smf")
expect(launcher_find_by_name("definitely_missing_simpleos_command")).to_equal(-1)
```

</details>

#### prefers staged /sys/apps payloads before PATH lookups

- Verify: prefers staged /sys/apps payloads before PATH lookups
   - Expected: candidates[0] equals `/sys/apps/info.smf`
   - Expected: candidates[1] equals `/sys/apps/info`
   - Expected: candidates[2] equals `/bin/info`
   - Expected: candidates[3] equals `/usr/bin/info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: prefers staged /sys/apps payloads before PATH lookups")
val candidates = launcher_command_resolution_candidates("info", "/", "/bin:/usr/bin")
expect(candidates[0]).to_equal("/sys/apps/info.smf")
expect(candidates[1]).to_equal("/sys/apps/info")
expect(candidates[2]).to_equal("/bin/info")
expect(candidates[3]).to_equal("/usr/bin/info")
```

</details>

#### normalizes migrated aliases before building sys-app candidates

- Verify: normalizes migrated aliases before building sys-app candidates
   - Expected: candidates[0] equals `/sys/apps/simple_browser.smf`
   - Expected: candidates[1] equals `/sys/apps/simple_browser`
   - Expected: compiler_candidates[0] equals `/sys/apps/simple_compiler.smf`
   - Expected: compiler_candidates[1] equals `/sys/apps/simple_compiler`
   - Expected: simple_candidates[0] equals `/sys/apps/simple.smf`
   - Expected: simple_candidates[1] equals `/sys/apps/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: normalizes migrated aliases before building sys-app candidates")
val candidates = launcher_command_resolution_candidates("sbrowser", "/", "")
expect(candidates[0]).to_equal("/sys/apps/simple_browser.smf")
expect(candidates[1]).to_equal("/sys/apps/simple_browser")

val compiler_candidates = launcher_command_resolution_candidates("scompiler.smf", "/", "")
expect(compiler_candidates[0]).to_equal("/sys/apps/simple_compiler.smf")
expect(compiler_candidates[1]).to_equal("/sys/apps/simple_compiler")

val simple_candidates = launcher_command_resolution_candidates("SIMPLSTC.smf", "/", "")
expect(simple_candidates[0]).to_equal("/sys/apps/simple.smf")
expect(simple_candidates[1]).to_equal("/sys/apps/simple")
```

</details>

#### keeps explicit paths ahead of catalog lookup

- Verify: keeps explicit paths ahead of catalog lookup
   - Expected: candidates.len() equals `1`
   - Expected: candidates[0] equals `/tmp/work/./info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: keeps explicit paths ahead of catalog lookup")
val candidates = launcher_command_resolution_candidates("./info", "/tmp/work", "/bin")
expect(candidates.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(candidates[0]).to_equal("/tmp/work/./info")
```

</details>

#### canonicalizes seeded process rows to stable sys-app identity

- Verify: canonicalizes seeded process rows to stable sys-app identity
   - Expected: launcher_record_process(pid, 7, "running", 0, 0, true) is true
   - Expected: launcher_get_process_path(0) equals `/sys/apps/simple_browser.smf`
   - Expected: launcher_get_process_app_id(0) equals `/sys/apps/simple_browser`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/simple_browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: canonicalizes seeded process rows to stable sys-app identity")
launcher_init()
val pid: u64 = 8022
expect(launcher_record_process(pid, 7, "running", 0, 0, true)).to_equal(true)
expect(launcher_get_process_path(0)).to_equal("/sys/apps/simple_browser.smf")
expect(launcher_get_process_app_id(0)).to_equal("/sys/apps/simple_browser")
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/simple_browser")
```

</details>

#### tracks process snapshots and window counts

- Verify: tracks process snapshots and window counts
   - Expected: seeded is true
   - Expected: launcher_get_running_app_count() equals `1`
   - Expected: launcher_is_running(demo_slot) is true
   - Expected: launcher_get_pid(demo_slot) equals `101`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `running`
   - Expected: launcher_get_app_window_count(demo_slot) equals `0`
   - Expected: launcher_get_app_is_headless(demo_slot) is true
   - Expected: launcher_get_process_count() equals `1`
   - Expected: launcher_get_running_process_count() equals `1`
   - Expected: launcher_get_process_pid(0) equals `101`
   - Expected: launcher_get_process_app_index(0) equals `demo_idx`
   - Expected: launcher_get_process_name(0) equals `Demo App`
   - Expected: launcher_get_process_path(0) equals `/apps/demo`
   - Expected: launcher_get_process_app_id(0) equals `/apps/demo`
   - Expected: launcher_get_process_app_id_for_pid(101) equals `/apps/demo`
   - Expected: launcher_get_process_icon(0) equals `D`
   - Expected: launcher_get_process_state(0) equals `running`
   - Expected: launcher_get_process_exit_code(0) equals `0`
   - Expected: launcher_get_process_window_count(0) equals `0`
   - Expected: launcher_get_process_is_headless(0) is true
   - Expected: launcher_get_process_launch_seq(0) equals `1`
   - Expected: launcher_process_is_process_backed(101) is true
   - Expected: launcher_get_app_window_count(demo_slot) equals `1`
   - Expected: launcher_get_app_is_headless(demo_slot) is false
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_process_is_headless(0) is false
   - Expected: launcher_get_app_window_count(demo_slot) equals `0`
   - Expected: launcher_get_app_is_headless(demo_slot) is true
   - Expected: launcher_get_process_window_count(0) equals `0`
   - Expected: launcher_get_process_is_headless(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: tracks process snapshots and window counts")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
val seeded = launcher_record_process(101, demo_idx, "running", 0, 0, true)
expect(seeded).to_equal(true)
expect(launcher_get_running_app_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_is_running(demo_slot)).to_equal(true)
expect(launcher_get_pid(demo_slot)).to_equal(101)  # oracle: 101 — named expected value from the requirement
expect(launcher_get_app_launch_state(demo_slot)).to_equal("running")
expect(launcher_get_app_window_count(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_is_headless(demo_slot)).to_equal(true)
expect(launcher_get_process_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_get_process_pid(0)).to_equal(101)  # oracle: 101 — named expected value from the requirement
expect(launcher_get_process_app_index(0)).to_equal(demo_idx)
expect(launcher_get_process_name(0)).to_equal("Demo App")
expect(launcher_get_process_path(0)).to_equal("/apps/demo")
expect(launcher_get_process_app_id(0)).to_equal("/apps/demo")
expect(launcher_get_process_app_id_for_pid(101)).to_equal("/apps/demo")
expect(launcher_get_process_icon(0)).to_equal("D")
expect(launcher_get_process_state(0)).to_equal("running")
expect(launcher_get_process_exit_code(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_window_count(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_is_headless(0)).to_equal(true)
expect(launcher_get_process_launch_seq(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_process_is_process_backed(101)).to_equal(true)

launcher_note_window_opened(101)
expect(launcher_get_app_window_count(demo_slot)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_get_app_is_headless(demo_slot)).to_equal(false)
expect(launcher_get_process_window_count(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_get_process_is_headless(0)).to_equal(false)

launcher_note_window_closed(101)
expect(launcher_get_app_window_count(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_is_headless(demo_slot)).to_equal(true)
expect(launcher_get_process_window_count(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_is_headless(0)).to_equal(true)
```

</details>

#### rejects synthetic and unknown pids as process-backed rows

- Verify: rejects synthetic and unknown pids as process-backed rows
   - Expected: launcher_process_is_process_backed(404) is false
   - Expected: launcher_record_process(0x40000010, -1, "running", 0, 0, true) is true
   - Expected: launcher_process_is_process_backed(0x40000010) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: rejects synthetic and unknown pids as process-backed rows")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
expect(launcher_process_is_process_backed(404)).to_equal(false)
expect(launcher_record_process(0x40000010, -1, "running", 0, 0, true)).to_equal(true)
expect(launcher_process_is_process_backed(0x40000010)).to_equal(false)
```

</details>

#### clears stale last launch state on init

- Verify: clears stale last launch state on init
   - Expected: launcher_record_process(101, 0, "running", 0, 0, true) is true
   - Expected: launcher_get_last_launch_pid() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: clears stale last launch state on init")
launcher_init()
expect(launcher_record_process(101, 0, "running", 0, 0, true)).to_equal(true)
launcher_init()
expect(launcher_get_last_launch_pid()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### keeps compacted registry rows after unregistering seeded apps

- Verify: keeps compacted registry rows after unregistering seeded apps
   - Expected: launcher_get_app_count() equals `10`
   - Expected: launcher_get_process_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: keeps compacted registry rows after unregistering seeded apps")
launcher_init()
launcher_unregister("Hello World")
launcher_unregister("File Manager")
launcher_unregister("Terminal")
launcher_unregister("Browser Demo")
launcher_unregister("Editor")
expect(launcher_get_app_count()).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(launcher_find_by_name("Simple Loader")).to_be_greater_than(-1)
expect(launcher_get_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### appends a new row when a kernel pid is reused after exit

- Verify: appends a new row when a kernel pid is reused after exit
   - Expected: launcher_record_process(505, demo_idx, "running", 0, 0, true) is true
   - Expected: launcher_record_process(505, demo_idx, "running", 0, 0, true) is true
   - Expected: launcher_get_process_count() equals `2`
   - Expected: launcher_get_process_state(0) equals `exited`
   - Expected: launcher_get_process_state(1) equals `running`
   - Expected: launcher_get_process_launch_seq(1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: appends a new row when a kernel pid is reused after exit")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
expect(launcher_record_process(505, demo_idx, "running", 0, 0, true)).to_equal(true)
launcher_mark_exited_with_code(505, 0)
expect(launcher_record_process(505, demo_idx, "running", 0, 0, true)).to_equal(true)
expect(launcher_get_process_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(launcher_get_process_state(0)).to_equal("exited")
expect(launcher_get_process_state(1)).to_equal("running")
expect(launcher_get_process_launch_seq(1)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### marks exits and preserves exit codes

- Verify: marks exits and preserves exit codes
   - Expected: launcher_get_pid(demo_slot) equals `0`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `exited`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `-1`
   - Expected: launcher_get_running_app_count() equals `0`
   - Expected: launcher_get_running_process_count() equals `0`
   - Expected: launcher_get_process_state(0) equals `exited`
   - Expected: launcher_get_process_exit_code(0) equals `-1`
   - Expected: launcher_get_process_is_headless(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: marks exits and preserves exit codes")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(101, demo_idx, "running", 0, 0, true)
launcher_mark_exited(101)
expect(launcher_get_pid(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_launch_state(demo_slot)).to_equal("exited")
expect(launcher_get_app_exit_code(demo_slot)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_state(0)).to_equal("exited")
expect(launcher_get_process_exit_code(0)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(launcher_get_process_is_headless(0)).to_equal(true)
```

</details>

#### stores explicit exit codes

- Verify: stores explicit exit codes
   - Expected: launcher_get_pid(demo_slot) equals `0`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `crashed`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `7`
   - Expected: launcher_get_running_app_count() equals `0`
   - Expected: launcher_get_running_process_count() equals `0`
   - Expected: launcher_get_process_state(0) equals `crashed`
   - Expected: launcher_get_process_exit_code(0) equals `7`
   - Expected: launcher_get_process_is_headless(0) is true
   - Expected: launcher_get_process_window_count(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: stores explicit exit codes")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(101, demo_idx, "running", 0, 0, true)
launcher_mark_exited_with_code(101, 7)
expect(launcher_get_pid(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_launch_state(demo_slot)).to_equal("crashed")
expect(launcher_get_app_exit_code(demo_slot)).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_state(0)).to_equal("crashed")
expect(launcher_get_process_exit_code(0)).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(launcher_get_process_is_headless(0)).to_equal(true)
expect(launcher_get_process_window_count(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### keeps terminate flows separate from crash exits

- Verify: keeps terminate flows separate from crash exits
   - Expected: launcher_get_process_state(0) equals `terminating`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `terminating`
   - Expected: launcher_get_pid(demo_slot) equals `0`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `terminated`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `15`
   - Expected: launcher_get_app_window_count(demo_slot) equals `0`
   - Expected: launcher_get_process_state(0) equals `terminated`
   - Expected: launcher_get_process_exit_code(0) equals `15`
   - Expected: launcher_get_process_window_count(0) equals `0`
   - Expected: launcher_get_process_is_headless(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: keeps terminate flows separate from crash exits")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(101, demo_idx, "running", 0, 2, false)
launcher_terminate(101)
expect(launcher_get_process_state(0)).to_equal("terminating")
expect(launcher_get_app_launch_state(demo_slot)).to_equal("terminating")
launcher_mark_exited_with_code(101, 15)
expect(launcher_get_pid(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_launch_state(demo_slot)).to_equal("terminated")
expect(launcher_get_app_exit_code(demo_slot)).to_equal(15)  # oracle: 15 — named expected value from the requirement
expect(launcher_get_app_window_count(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_state(0)).to_equal("terminated")
expect(launcher_get_process_exit_code(0)).to_equal(15)  # oracle: 15 — named expected value from the requirement
expect(launcher_get_process_window_count(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_process_is_headless(0)).to_equal(true)
```

</details>

#### fails terminate requests without mutating registry state

- Verify: fails terminate requests without mutating registry state
   - Expected: terminated is false
   - Expected: launcher_get_process_state(0) equals `running`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `running`
   - Expected: launcher_get_running_process_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: fails terminate requests without mutating registry state")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(101, demo_idx, "running", 0, 0, true)
val terminated = launcher_terminate(999999)
expect(terminated).to_equal(false)
expect(launcher_get_process_state(0)).to_equal("running")
expect(launcher_get_app_launch_state(demo_slot)).to_equal("running")
expect(launcher_get_running_process_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### compacts registry and keeps process app indices aligned

- Verify: compacts registry and keeps process app indices aligned
   - Expected: removed is true
   - Expected: launcher_find_by_name("Demo A") equals `-1`
   - Expected: shifted_b_idx equals `demo_a_idx`
   - Expected: launcher_get_app_count() equals `16`
   - Expected: launcher_get_app_name(shifted_b_idx.to_u64()) equals `Demo B`
   - Expected: launcher_get_process_count() equals `2`
   - Expected: launcher_find_process_by_pid(202) equals `1`
   - Expected: launcher_get_process_app_index(1) equals `shifted_b_idx`
   - Expected: launcher_get_process_name(1) equals `Demo B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: compacts registry and keeps process app indices aligned")
launcher_init()
launcher_register("Demo A", "/apps/demo_a", "A", 0x41, MOD_META)
launcher_register("Demo B", "/apps/demo_b", "B", 0x42, MOD_META)
val demo_a_idx = launcher_find_by_name("Demo A")
val demo_b_idx = launcher_find_by_name("Demo B")
launcher_record_process(201, demo_a_idx, "running", 0, 0, true)
launcher_record_process(202, demo_b_idx, "running", 0, 0, true)
val removed = launcher_unregister("Demo A")
expect(removed).to_equal(true)
expect(launcher_find_by_name("Demo A")).to_equal(-1)
val shifted_b_idx = launcher_find_by_name("Demo B")
expect(shifted_b_idx).to_equal(demo_a_idx)
expect(launcher_get_app_count()).to_equal(16)  # oracle: 16 — named expected value from the requirement
expect(launcher_get_app_name(shifted_b_idx.to_u64())).to_equal("Demo B")
expect(launcher_get_process_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(launcher_find_process_by_pid(202)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(launcher_get_process_app_index(1)).to_equal(shifted_b_idx)
expect(launcher_get_process_name(1)).to_equal("Demo B")
```

</details>

### Launcher task reaper

#### leaves live probes untouched

- Verify: leaves live probes untouched
   - Expected: launcher_get_process_state(0) equals `running`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `running`
   - Expected: launcher_get_running_process_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: leaves live probes untouched")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(301, demo_idx, "running", 0, 0, true)
launcher_note_task_probe(301, true, 0)
expect(launcher_get_process_state(0)).to_equal("running")
expect(launcher_get_app_launch_state(demo_slot)).to_equal("running")
expect(launcher_get_running_process_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### marks graceful exits as exited with the reported code

- Verify: marks graceful exits as exited with the reported code
   - Expected: launcher_get_process_state(0) equals `exited`
   - Expected: launcher_get_process_exit_code(0) equals `0`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `exited`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `0`
   - Expected: launcher_get_app_window_count(demo_slot) equals `0`
   - Expected: launcher_get_running_process_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: marks graceful exits as exited with the reported code")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(302, demo_idx, "running", 0, 1, false)
launcher_note_task_probe(302, false, 0)
expect(launcher_get_process_state(0)).to_equal("exited")
expect(launcher_get_process_exit_code(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_launch_state(demo_slot)).to_equal("exited")
expect(launcher_get_app_exit_code(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_app_window_count(demo_slot)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### marks unexpected exits with nonzero code as crashed

- Verify: marks unexpected exits with nonzero code as crashed
   - Expected: launcher_get_process_state(0) equals `crashed`
   - Expected: launcher_get_process_exit_code(0) equals `11`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `crashed`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `11`
   - Expected: launcher_get_running_process_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: marks unexpected exits with nonzero code as crashed")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(303, demo_idx, "running", 0, 0, true)
launcher_note_task_probe(303, false, 11)
expect(launcher_get_process_state(0)).to_equal("crashed")
expect(launcher_get_process_exit_code(0)).to_equal(11)  # oracle: 11 — named expected value from the requirement
expect(launcher_get_app_launch_state(demo_slot)).to_equal("crashed")
expect(launcher_get_app_exit_code(demo_slot)).to_equal(11)  # oracle: 11 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### finalizes terminating processes as terminated

- Verify: finalizes terminating processes as terminated
   - Expected: launcher_get_process_state(0) equals `terminating`
   - Expected: launcher_get_process_state(0) equals `terminated`
   - Expected: launcher_get_app_launch_state(demo_slot) equals `terminated`
   - Expected: launcher_get_app_exit_code(demo_slot) equals `15`
   - Expected: launcher_get_running_process_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: finalizes terminating processes as terminated")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
val demo_slot = demo_idx.to_u64()
launcher_record_process(304, demo_idx, "running", 0, 0, true)
launcher_terminate(304)
expect(launcher_get_process_state(0)).to_equal("terminating")
launcher_note_task_probe(304, false, 15)
expect(launcher_get_process_state(0)).to_equal("terminated")
expect(launcher_get_app_launch_state(demo_slot)).to_equal("terminated")
expect(launcher_get_app_exit_code(demo_slot)).to_equal(15)  # oracle: 15 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### is idempotent across repeated probes for the same dead pid

- Verify: is idempotent across repeated probes for the same dead pid
   - Expected: launcher_get_process_state(0) equals `crashed`
   - Expected: launcher_get_process_exit_code(0) equals `9`
   - Expected: launcher_get_running_process_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: is idempotent across repeated probes for the same dead pid")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
launcher_record_process(305, demo_idx, "running", 0, 0, true)
launcher_note_task_probe(305, false, 9)
launcher_note_task_probe(305, false, 9)
launcher_note_task_probe(305, false, 9)
expect(launcher_get_process_state(0)).to_equal("crashed")
expect(launcher_get_process_exit_code(0)).to_equal(9)  # oracle: 9 — named expected value from the requirement
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### ignores probes for unknown pids

- Verify: ignores probes for unknown pids
   - Expected: launcher_get_process_state(0) equals `running`
   - Expected: launcher_get_running_process_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: ignores probes for unknown pids")
launcher_init()
launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
val demo_idx = launcher_find_by_name("Demo App")
launcher_record_process(306, demo_idx, "running", 0, 0, true)
launcher_note_task_probe(999999, false, 1)
expect(launcher_get_process_state(0)).to_equal("running")
expect(launcher_get_running_process_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-SERVICES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `530ff7fed2dac52e9fb110e4ade68936f1aef1cf5312ba7f7abfd7f7ac7651ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `530ff7fed2dac52e9fb110e4ade68936f1aef1cf5312ba7f7abfd7f7ac7651ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `530ff7fed2dac52e9fb110e4ade68936f1aef1cf5312ba7f7abfd7f7ac7651ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/services/launcher/launcher_spec.spl
mirror: doc/06_spec/unit/os/services/launcher/launcher_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/os/services/launcher/launcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/launcher/launcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/launcher/launcher_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/services/launcher/launcher_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/services/launcher/launcher_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seeds built-in apps with manifest-backed binary identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/launcher/launcher_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers apps with idle launch state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/launcher/launcher_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps text and image files to the default opener app' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
