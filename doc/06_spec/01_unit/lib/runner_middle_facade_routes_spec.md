# Runner middle facade routes

- Executable spec: `test/01_unit/lib/runner_middle_facade_routes_spec.spl`
- Source SHA-256: `362b26295de59fbbb8b6e63c811a655c9a98547c2775df1166a9f297c4f8d1a4`
- Manual status: hand-maintained source mirror; no test-run receipt is asserted.
- Scenarios: 4 active, 0 skipped, 0 pending.

## Scope

These scenarios pin the source-level export paths used by the Stage2 test runner. They check explicit owner and facade names; a passing runtime import and the six compiler, interpreter, and loader test rows still require an admitted tool build.

## Shared setup

```simple
# Runner HIR import routes must stay visible through the no-GC async facades.
# This is a source contract for the exact facade hops used by the Stage2 runner.

use std.spec.{describe, it, expect}
use std.spec.step

extern fn rt_file_read_text(path: text) -> text?

fn facade_source(path: text) -> text:
    rt_file_read_text(path) ?? ""
```

## Scenarios

### 1. exports parsing evidence and coverage names from their sync owner

Confirms the sync owner declares and exports the temp-directory helper, and the async facade carries the structured-evidence, MCDC, and compiler-coverage names.

```simple
    it "exports parsing evidence and coverage names from their sync owner":
        step("Read the sync parsing owner and its no-GC async facade")
        val owner = facade_source("src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl")
        val facade = facade_source("src/lib/nogc_async_mut/test_runner/test_executor_parsing.spl")
        expect(owner).to_contain("fn _tp_get_temp_dir()")
        expect(owner).to_contain("export _tp_get_temp_dir")
        expect(facade).to_start_with("export use std.nogc_sync_mut.test_runner.test_executor_parsing.")
        expect(facade).to_contain("make_result_from_structured_evidence")
        expect(facade).to_contain("extract_compiler_mcdc_obligation_manifest")
        expect(facade).to_contain("_tp_get_temp_dir")
        expect(facade).to_contain("COMPILER_COVERAGE_BEGIN, COMPILER_COVERAGE_END")
```

### 2. exports redirected spawn and container runtime through their async facades

Confirms redirected child spawning and container-runtime discovery remain available through the no-GC async runner facades.

```simple
    it "exports redirected spawn and container runtime through their async facades":
        step("Read the lifecycle and process-tracker facade hops")
        val lifecycle = facade_source("src/lib/nogc_async_mut/test_runner/runner_lifecycle.spl")
        val tracker = facade_source("src/lib/nogc_async_mut/test_runner/process_tracker.spl")
        expect(lifecycle).to_start_with("export use std.nogc_sync_mut.test_runner.runner_lifecycle.")
        expect(lifecycle).to_contain("spawn_tracked_redirected_process")
        expect(tracker).to_start_with("export use std.nogc_sync_mut.test_runner.process_tracker.")
        expect(tracker).to_contain("tracker_container_runtime")
```

### 3. exports nonblocking Vulkan submission through the async tier

Confirms the GC async Vulkan lane can reach the sync owner’s nonblocking submission API through its no-GC async facade.

```simple
    it "exports nonblocking Vulkan submission through the async tier":
        step("Read the Vulkan facade used by the GC async lane")
        val owner = facade_source("src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl")
        val facade = facade_source("src/lib/nogc_async_mut/gpu/engine2d/sffi_vulkan.spl")
        expect(owner).to_contain("fn vulkan_sffi_submit_no_wait(")
        expect(facade).to_contain("export use std.nogc_sync_mut.gpu.engine2d.sffi_vulkan.")
        expect(facade).to_contain("vulkan_sffi_submit_no_wait")
```

### 4. exports database tracking helpers and runtime identity names

Confirms database tracking helpers and runtime-identity names are exported through the database and stubs facades, without the nonexistent `rt_*` aliases.

```simple
    it "exports database tracking helpers and runtime identity names":
        step("Read the database and stubs facade hops")
        val database = facade_source("src/lib/nogc_async_mut/database/test_extended/database.spl")
        val stubs = facade_source("src/lib/nogc_async_mut/database/test_extended/stubs.spl")
        val package = facade_source("src/lib/nogc_async_mut/database/test_extended/__init__.spl")
        expect(database).to_start_with("export use nogc_sync_mut.database.test_extended.database.")
        expect(database).to_contain("trim_to_last_f64")
        expect(database).to_contain("ensure_timing_baseline_schema")
        expect(database).to_contain("TIMING_RUNS_PER_TEST_CAP")
        expect(stubs).to_contain(r"export use nogc_sync_mut.database.test_extended.stubs.{timestamp_now, process_id, host_name}")
        expect(package).to_contain(r"export use nogc_async_mut.database.test_extended.stubs.{timestamp_now, process_id, host_name}")
        expect(stubs.contains("rt_timestamp_now")).to_equal(false)
        expect(stubs.contains("rt_getpid")).to_equal(false)
```

## Verification

Run `test/01_unit/lib/runner_middle_facade_routes_spec.spl` with an admitted Simple test runner and require a nonzero-execution `Results:` receipt. No such runtime result is claimed by this manual.
