# Application Writing Guide

**Purpose:** Guide for building Simple applications with links to language manuals and generated specs.

---

## Overview

This guide covers building applications in Simple with references to:
- Generated specification documents
- Language manuals
- GUI/TUI framework guides

---

## Quick Start

### 1. Project Structure

```
my_app/
├── __init__.spl           # Module manifest
├── main.spl               # Entry point
├── config.spl             # Configuration
├── domain/                # Domain types
│   ├── __init__.spl
│   └── models.spl
├── service/               # Application services
│   ├── __init__.spl
│   └── handlers.spl
└── test/                  # Tests
    └── app_spec.spl
```

### 2. Entry Point

```simple
# main.spl
import config.{AppConfig, load_config}
import service.{start_server}

fn main():
    config = load_config()
    start_server(config)
```

---

## Language Reference

### Core Language Specs

| Topic | Manual | Generated Spec |
|-------|--------|----------------|
| **Syntax** | [doc/spec/syntax.md](../spec/syntax.md) | [generated/syntax.md](../spec/generated/syntax.md) |
| **Types** | [doc/spec/types.md](../spec/types.md) | [generated/types.md](../spec/generated/types.md) |
| **Functions** | [doc/spec/functions.md](../spec/functions.md) | [generated/functions.md](../spec/generated/functions.md) |
| **Traits** | [doc/spec/traits.md](../spec/traits.md) | [generated/traits.md](../spec/generated/traits.md) |
| **Memory** | [doc/spec/memory.md](../spec/memory.md) | [generated/memory.md](../spec/generated/memory.md) |
| **Modules** | [doc/spec/modules.md](../spec/modules.md) | [generated/modules.md](../spec/generated/modules.md) |

### Advanced Features

| Topic | Manual | Generated Spec |
|-------|--------|----------------|
| **Async/Await** | [doc/spec/async_default.md](../spec/async_default.md) | [generated/async_default.md](../spec/generated/async_default.md) |
| **Concurrency** | [doc/spec/concurrency.md](../spec/concurrency.md) | [generated/concurrency.md](../spec/generated/concurrency.md) |
| **Capabilities** | [doc/spec/capability_effects.md](../spec/capability_effects.md) | [generated/capability_effects.md](../spec/generated/capability_effects.md) |
| **Metaprogramming** | [doc/spec/metaprogramming.md](../spec/metaprogramming.md) | [generated/metaprogramming.md](../spec/generated/metaprogramming.md) |
| **Macros** | [doc/spec/macro.md](../spec/macro.md) | [generated/macro.md](../spec/generated/macro.md) |
| **Data Structures** | [doc/spec/data_structures.md](../spec/data_structures.md) | [generated/data_structures.md](../spec/generated/data_structures.md) |

### Testing

| Topic | Manual |
|-------|--------|
| **SSpec Manual** | [doc/spec/sspec_manual.md](../spec/sspec_manual.md) |
| **BDD Framework** | [doc/spec/testing/testing_bdd_framework.md](../spec/testing/testing_bdd_framework.md) |
| **Doctest** | [doc/spec/testing/sdoctest.md](../spec/testing/sdoctest.md) |
| **Mock Framework** | [doc/spec/testing/mock.md](../spec/testing/mock.md) |

### Generated Specs Index

Full index of all generated specifications:
- **[doc/spec/generated/README.md](../spec/generated/README.md)** - Index with 16 specs, 292 tests

---

## GUI Applications

### Framework Options

| Framework | Use Case | Spec |
|-----------|----------|------|
| **TUI** | Terminal UI | [doc/spec/tui.md](../spec/tui.md) |
| **Vulkan GUI** | Native GPU UI | [doc/guide/vulkan_backend.md](vulkan_backend.md) |
| **Electron** | Desktop apps | [doc/guide/ui.md](ui.md) |
| **Web** | Browser apps | [doc/spec/web.md](../spec/web.md) |

### TUI Application

```simple
# tui_app.spl
import std.ui.tui.{App, Frame, Text, Input, render}

class MyApp:
    impl App:
        fn render(self, frame: Frame):
            frame.draw(Text.new("Hello TUI!").centered())

        fn handle_input(mut self, key: Key) -> Action:
            match key:
                case Key.Q => Action.Quit
                case _ => Action.Continue

fn main():
    app = MyApp.new()
    render(app)
```

### Vulkan GUI Application

```simple
# vulkan_app.spl
import std.ui.gui.vulkan.{Window, Renderer, Button, Text}

class MyWindow:
    renderer: Renderer

    fn new() -> MyWindow:
        renderer = Renderer.new(800, 600, "My App")
        MyWindow { renderer }

    fn run(mut self):
        while not self.renderer.should_close():
            self.renderer.begin_frame()

            # UI components
            if Button.new("Click Me").render():
                print("Clicked!")

            Text.new("Hello Vulkan!").render()

            self.renderer.end_frame()

fn main():
    window = MyWindow.new()
    window.run()
```

### Screenshot and Diagram Generation

Generate screenshots and diagrams from GUI tests:

```simple
# test/gui_spec.spl
import std.spec
import std.spec.screenshot.{capture_screenshot, compare_screenshot}
import diagram.integration.{with_sequence_diagram}

describe "MyApp GUI":
    @architectural
    context "main window":
        it "renders correctly":
            app = MyApp.new()
            app.render()

            # Capture screenshot for documentation
            capture_screenshot("main_window", app.renderer)

        it "handles button click":
            with_sequence_diagram("button_click") \:
                app = MyApp.new()
                app.click_button("submit")
                expect app.state to eq "submitted"
```

Run with screenshot capture:
```bash
simple test gui_spec.spl --screenshot-output doc/spec/image/
```

---

## Web Applications

### Web Framework

```simple
# web_app.spl
import std.web.{Server, Router, Request, Response, Json}

router = Router.new()
    .get("/") \req:
        Response.html("<h1>Hello Web!</h1>")
    .get("/api/users") \req:
        users = UserService.list()
        Response.json(users)
    .post("/api/users") \req:
        user = req.json[CreateUser]()
        created = UserService.create(user)
        Response.json(created).status(201)

fn main():
    server = Server.new(router)
    server.listen(8080)
```

See: [doc/spec/web.md](../spec/web.md)

---

## CLI Applications

### Argument Parsing

```simple
# cli_app.spl
import std.cli.{Args, Command, Flag}

fn main():
    cmd = Command.new("myapp")
        .version("1.0.0")
        .about("My CLI application")
        .flag(Flag.new("verbose").short("v").help("Enable verbose output"))
        .arg(Arg.new("input").required().help("Input file"))

    args = cmd.parse()

    if args.has("verbose"):
        print("Verbose mode enabled")

    input_file = args.get("input")
    process(input_file)
```

See: [doc/spec/generated/shell_api.md](../spec/generated/shell_api.md)

---

## Database Applications

### Database Connection

```simple
# db_app.spl
import std.db.{Database, Query, migrate}

fn main():
    db = Database.connect("postgres://localhost/myapp")

    # Run migrations
    migrate(db, "migrations/")

    # Query
    users = db.query("SELECT * FROM users WHERE active = $1", [true])
        .map(User.from_row)
        .collect()

    for user in users:
        print("User: {user.name}")
```

See: [doc/guide/db.md](db.md)

---

## Configuration Patterns

### Multi-Source Config

```simple
# config.spl
import std.config.{Config, ConfigLoader}
import std.env

struct AppConfig:
    host: String
    port: u16
    debug: Bool
    database_url: String

    fn new() -> AppConfig:
        AppConfig {
            host: "localhost",
            port: 8080,
            debug: false,
            database_url: "postgres://localhost/app"
        }

fn load_config() -> AppConfig:
    # Load hierarchy: defaults → file → env → cli
    ConfigLoader.new()
        .with_defaults(AppConfig.new())
        .with_file("config.toml")
        .with_env_prefix("APP_")
        .with_cli_args()
        .load()
```

See: [coding_style.md](coding_style.md#configuration-patterns)

---

## Application Testing

### Integration Test Structure

```simple
# test/integration/app_spec.spl
import std.spec
import std.spec.screenshot.*
import diagram.integration.*

describe "MyApplication":
    """
    ## Application Integration Tests

    Tests with diagram and screenshot generation.
    """

    before_all:
        # Setup test database
        @db = TestDatabase.create()

    after_all:
        @db.drop()

    @architectural
    @record_diagram(name: "UserRegistration")
    context "user registration flow":
        it "creates user and sends welcome email":
            with_all_diagrams("user_registration") \:
                # Interactions recorded for sequence diagram
                user = UserService.register("alice@example.com", "password")
                expect user to not_be_nil

                # Check email was sent
                emails = MockMailer.sent_emails()
                expect emails.len() to eq 1
                expect emails[0].to to eq "alice@example.com"

    context "GUI rendering":
        it "shows dashboard after login":
            app = TestApp.new()
            app.login("alice@example.com", "password")

            # Capture screenshot
            capture_screenshot("dashboard", app.current_view())

            expect app.current_route() to eq "/dashboard"
```

### Running Application Tests

```bash
# Run with all outputs
simple test test/integration/app_spec.spl \
    --diagram-all \
    --diagram-output doc/spec/diagrams/ \
    --screenshot-output doc/spec/image/

# Generated files:
# doc/spec/diagrams/user_registration_sequence.md
# doc/spec/diagrams/user_registration_class.md
# doc/spec/image/dashboard.png
```

---

## Documentation Generation

### From Tests to Docs

Tests generate documentation artifacts:

```
test/app_spec.spl
    │
    ├── Run with --diagram-all
    │   └── doc/spec/diagrams/
    │       ├── feature_sequence.md
    │       └── feature_class.md
    │
    ├── Run with --screenshot-output
    │   └── doc/spec/image/
    │       └── feature_screenshot.png
    │
    └── doctest extraction
        └── doc/spec/generated/
            └── feature.md
```

### Link Generated Assets in README

```markdown
# My Application

## Architecture

See: [Architecture Diagram](doc/spec/diagrams/app_arch.md)

## Screenshots

### Dashboard
![Dashboard](doc/spec/image/dashboard.png)

### User Registration Flow
```mermaid
sequenceDiagram
    ... (from generated/user_registration_sequence.md)
```
```

---

## Quick Reference

### Spec Locations

| Type | Location |
|------|----------|
| Language specs | `doc/spec/*.md` |
| Generated specs | `doc/spec/generated/*.md` |
| Test specs | `tests/specs/*_spec.spl` |
| Generated diagrams | `target/diagrams/` or `doc/spec/diagrams/` |
| Screenshots | `doc/spec/image/` |

### Commands

```bash
# Run application
simple run main.spl

# Run with config
simple run main.spl --config production.toml

# Run tests
simple test test/

# Generate docs from tests
simple test --diagram-all --screenshot-output doc/spec/image/

# Build release
simple build --release
```

---

## See Also

### Guides
- [coding_style.md](coding_style.md) - Coding conventions
- [design_writing.md](design_writing.md) - Design with diagrams
- [architecture_writing.md](architecture_writing.md) - Architecture patterns
- [sspec_writing.md](sspec_writing.md) - Test writing

### Specs
- [doc/spec/README.md](../spec/README.md) - All specifications index
- [doc/spec/generated/README.md](../spec/generated/README.md) - Generated specs index
- [doc/spec/sspec_manual.md](../spec/sspec_manual.md) - SSpec user manual

### Framework Guides
- [ui.md](ui.md) - UI framework overview
- [web_framework.md](web_framework.md) - Web framework
- [db.md](db.md) - Database integration
- [vulkan_backend.md](vulkan_backend.md) - Vulkan GPU backend
