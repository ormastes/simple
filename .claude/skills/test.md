# Test Writing Skill

## Critical Rules

**NEVER ignore tests without explicit user approval:**
- Do NOT comment out test code
- Do NOT skip failing tests as a "fix"
- ALWAYS fix root cause or ask user

## Running Tests

```bash
bin/simple test                          # All tests
bin/simple test path/to/spec.spl         # Single test file
bin/simple test --list                   # List tests without running
bin/simple test --only-slow              # Run slow tests
bin/simple test --tag=integration        # Filter by tag
```

## Container Testing (Safe / Isolated)

Prefer container testing to avoid side effects on the host environment.

```bash
# Build image (once)
docker build -t simple-test-isolation:latest -f tools/docker/Dockerfile.test-isolation .

# Run tests in container (read-only workspace mount)
docker run --rm -v $(pwd):/workspace:ro --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test                   # All tests
docker run --rm -v $(pwd):/workspace:ro --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/        # Unit tests only

# Docker Compose (easiest for local development)
docker-compose -f config/docker-compose.yml up unit-tests         # Unit tests
docker-compose -f config/docker-compose.yml up integration-tests  # Integration tests
docker-compose -f config/docker-compose.yml up system-tests       # System tests
docker-compose -f config/docker-compose.yml up all-tests          # All tests parallel
docker-compose -f config/docker-compose.yml run dev-shell         # Interactive shell

# Helper scripts
scripts/local-container-test.sh unit                       # Unit tests in container
scripts/local-container-test.sh quick path/to/spec.spl    # Single test
scripts/local-container-test.sh shell                      # Interactive debugging
scripts/ci-test.sh                                         # CI-style execution
```

### Container Testing Troubleshooting

**Container not found:** `docker build -t simple-test-isolation:latest -f tools/docker/Dockerfile.test-isolation .`
**Permission denied:** `chmod +x bin/release/simple` or `sudo usermod -aG docker $USER && newgrp docker`
**Out of memory:** Increase `--memory=512m` to `--memory=1g` or `--memory=2g`
**Timeout errors:** Use correct profile: `--profile=slow` (10 min) or `--profile=intensive` (30 min)
**Tests pass locally, fail in CI:** Run exact CI command: `scripts/ci-test.sh test/unit/`

**Volume mount not working (Windows):**
- PowerShell: `docker run -v ${PWD}:/workspace:ro ...`
- CMD: `docker run -v %cd%:/workspace:ro ...`

**Container build fails:**
- Check runtime exists: `ls -lh bin/release/simple` (should be ~33MB)
- If missing: `scripts/install.sh` or download from releases

**jq not installed (parse errors):**
- Ubuntu: `sudo apt install jq`
- macOS: `brew install jq`

**Docker daemon not running:**
- Linux: `sudo systemctl start docker`
- macOS/Windows: Start Docker Desktop

```bash
# Docker Compose cleanup
docker-compose -f config/docker-compose.yml run dev-shell
# Inside: simple test test/unit/failing_spec.spl --verbose
docker-compose build --no-cache     # Rebuild after Dockerfile changes
docker-compose down                 # Stop services
docker system prune -a              # Remove all containers/images
```

**Full Guide:** `doc/guide/testing/container_testing.md` | **Test Config:** `simple.test.sdn`

## Writing Simple BDD Tests

Tests go in `test/` directory. Use `*_spec.spl` naming.

**CRITICAL: Use docstring markdown, NOT println() for test documentation!**

```simple
# feature_spec.spl

describe "Feature":
    """
    # Feature Module

    Provides core functionality for X, Y, Z.

    ## Overview
    - Feature A does X
    - Feature B does Y

    ## Usage
    ```simple
    val f = Feature(value: 10)
    f.increment()
    ```
    """

    context "when initialized":
        """
        Tests default initialization behavior.
        Ensures all fields start with correct values.
        """

        it "should have default value":
            """
            Default constructor should initialize value to 0.

            **Expected:** value = 0
            **Actual:** Verified via expect() assertion
            """
            val f = Feature(value: 0)
            expect(f.value).to_equal(0)

    context "with operations":
        """
        Tests arithmetic operations on Feature.

        ## Tested Operations
        - increment(): adds 1
        - decrement(): subtracts 1
        - add(n): adds n
        """

        it "should increment":
            """
            Increment operation should add 1 to current value.

            Given: Feature with value 10
            When: increment() is called
            Then: value should be 11
            """
            val f = Feature(value: 10)
            f.increment()
            expect(f.value).to_equal(11)
```

**Documentation Guidelines:**
- **Every `describe` block**: Rich markdown overview with usage examples
- **Every `context` block**: Explain what scenario/condition is being tested
- **Every `it` block**: Document expected behavior, inputs, outputs
- **Use markdown**: Headers, lists, code blocks, tables
- **NO println()**: All explanations go in docstrings, not print statements
- **Auto-generate docs**: SSpec uses docstrings for spec documentation

## Test File Naming

- Simple: `*_spec.spl` or `*_test.spl`
- Tests directory: `test/`
- Feature specs: `src/lib/test/features/`

## Test Types

| Type | Syntax | Behavior |
|------|--------|----------|
| Regular | `it "..."` | Runs by default |
| Slow | `slow_it "..."` | Auto-ignored, run with `--only-slow` |
| Skipped | `skip("name", "reason")` | Not yet implemented |

## Matchers Reference

Built-in runtime matchers only:

| Matcher | Usage |
|---------|-------|
| `to_equal(val)` | `expect(x).to_equal(5)` |
| `to_be(val)` | `expect(x).to_be(5)` |
| `to_be_nil()` | `expect(x).to_be_nil()` |
| `to_contain(item)` | `expect(list).to_contain(5)` |
| `to_start_with(s)` | `expect(text).to_start_with("he")` |
| `to_end_with(s)` | `expect(text).to_end_with("lo")` |
| `to_be_greater_than(n)` | `expect(x).to_be_greater_than(5)` |
| `to_be_less_than(n)` | `expect(x).to_be_less_than(10)` |

**Note:** `to_be_true`/`to_be_false` are NOT built-in. Use `to_equal(true)` / `to_equal(false)` instead.

## Run Tracking

Test results are automatically tracked in `doc/tracking/test/test_db.sdn`.

```bash
bin/simple test --list-runs              # View run history
bin/simple test --cleanup-runs           # Clean stale runs
bin/simple test --prune-runs=50          # Keep 50 most recent
```

Reports are generated at `doc/tracking/test/test_result.md` after every test run.

## UI System Testing (Headless Web-Port)

Test TUI and Web UI backends in headless environments via web ports. Both backends expose a shared Test API on localhost, and a `UITestClient` library provides click/type/drag/check operations.

### Architecture

```
System Test (SSpec) → UITestClient → HTTP → Web Backend (port 8080)
                                          → TUI Web Proxy (port 8081)
```

- **Web backend** (`ui.web`): Renders widget HTML, serves on port
- **TUI web proxy** (`ui.tui_web`): Renders TUI Screen buffer as `<pre>` with ANSI→CSS color mapping, serves on port
- **Test API** (`ui.test_api`): Shared module, localhost-only by default, `--test-api-external` for `0.0.0.0`

### Starting UI Servers for Testing

```bash
# Web backend with test API (localhost only)
bin/simple ui web examples/ui/demo_kitchen_sink.ui.sdn --port 9001

# TUI over web (headless-friendly, terminal emulator style)
bin/simple ui tui_web examples/ui/demo_kitchen_sink.ui.sdn --port 9000

# Allow external access to test API
bin/simple ui web app.ui.sdn --port 9001 --test-api-external
```

### UITestClient Library

```simple
use std.nogc_sync_mut.ui_test.client.{UITestClient}
use std.nogc_sync_mut.ui_test.types.{ElementInfo, UIStateInfo}

val client = UITestClient.connect("127.0.0.1", 9001)?

# Wait for server readiness
client.wait_ready(5000)?

# Actions
client.click("action_btn")?
client.type_text("search_input", "hello")?
client.drag("item_1", "target_panel")?
client.send_key("enter")?

# Queries
val elem = client.get_element("action_btn")?
val elems = client.get_elements()?
val state = client.get_state()?
val html = client.screenshot_html()?

# Assertions (convenience)
client.check_text("status_label", "Saved")?
client.check_visible("sidebar")?
client.check_focused("search_input")?
client.check_exists("nav_tabs")?

# Waiting
client.wait_for("modal_dialog", 3000)?
```

### Test API Endpoints

| Method | Path | Body | Response |
|--------|------|------|----------|
| POST | `/api/test/click` | `{"id":"X"}` | Focus + enter events |
| POST | `/api/test/type` | `{"id":"X","text":"hello"}` | Focus + keypress events |
| POST | `/api/test/drag` | `{"from_id":"X","to_id":"Y"}` | Synthetic drag events |
| POST | `/api/test/event` | `{"event_type":"key","key":"q"}` | Raw UIEvent injection |
| GET | `/api/test/screenshot` | — | Full HTML snapshot |
| GET | `/api/test/element?id=X` | — | `{"id","kind","visible","focused","props"}` |
| GET | `/api/test/elements` | — | All widgets JSON array |
| GET | `/api/test/ready` | — | `{"ready":true}` |

### Writing UI System Tests

```simple
# test/system/ui/my_app_spec.spl
# tag: slow, system

use std.nogc_sync_mut.ui_test.client.{UITestClient}

extern fn rt_process_spawn_async(cmd: text, args: [text]) -> i64
extern fn rt_process_kill(pid: i64) -> bool
extern fn rt_thread_sleep(ms: i64)

val port = 19042

describe "My App UI":
    it "clicks button and checks status":
        val pid = rt_process_spawn_async("bin/simple",
            ["ui", "web", "test/fixtures/ui/test_app.ui.sdn", "--port", "{port}"])
        rt_thread_sleep(1000)

        val client = UITestClient.connect("127.0.0.1", port)
        match client:
            Ok(c):
                c.wait_ready(5000)
                c.click("action_btn")
                val focused = c.check_focused("action_btn")
                expect(focused.is_ok()).to_equal(true)
                rt_process_kill(pid)
            Err(e):
                rt_process_kill(pid)
                expect(e).to_equal("")
```

### Test Helpers

Use `test/system/ui/helpers/ui_test_helpers.spl`:
- `start_ui_server(mode, sdn_file, port) -> i64` — spawns server, returns PID
- `stop_ui_server(pid)` — kills server
- `free_port() -> i32` — PID-based port to avoid conflicts

### Key Files

| File | Purpose |
|------|---------|
| `src/app/ui.test_api/handler.spl` | Shared test API handler |
| `src/app/ui.tui_web/` | TUI web proxy backend |
| `src/lib/nogc_sync_mut/ui_test/client.spl` | UITestClient library |
| `src/lib/nogc_sync_mut/ui_test/types.spl` | ElementInfo, UIStateInfo |
| `test/system/ui/helpers/ui_test_helpers.spl` | Test setup helpers |

## See Also

- `/sspec` skill - Full SSpec BDD framework details
- `.claude/templates/sspec_template.spl` - Template for new specs
- `doc/guide/testing/testing.md` - Testing guide (includes SSpec + UI testing)
- `doc/spec/testing/` - Testing framework specs
