# Simple Web Framework - User Guide

**Version:** 1.0
**Date:** 2025-12-25
**Status:** Production Ready

## Table of Contents

1. [Introduction](#introduction)
2. [Getting Started](#getting-started)
3. [.sui File Format](#sui-file-format)
4. [Building Web Applications](#building-web-applications)
5. [Development Server](#development-server)
6. [Hydration & Event Binding](#hydration--event-binding)
7. [Optimization](#optimization)
8. [Best Practices](#best-practices)
9. [Troubleshooting](#troubleshooting)
10. [API Reference](#api-reference)

---

## Introduction

The Simple Web Framework enables you to build **server-rendered web applications** with **client-side interactivity** using a unified `.sui` file format. It combines:

- **Server-Side Rendering (SSR)** - Generate HTML on the server for fast initial page loads
- **WebAssembly Compilation** - Compile client code to WASM for browser execution
- **Hydration** - Automatically attach event handlers to server-rendered DOM

**Key Features:**
- ✅ Single-file components (`.sui`)
- ✅ Shared state between server and client
- ✅ Automatic WASM compilation
- ✅ Zero-config hydration
- ✅ Development server with auto-rebuild
- ✅ Production optimization (WASM + HTML minification)

---

## Getting Started

### Prerequisites

1. **Simple Compiler** - Build from source:
   ```bash
   git clone https://github.com/simple-lang/simple
   cd simple
   cargo build --release
   ```

2. **wasm-opt** (optional, for optimization):
   ```bash
   # Ubuntu/Debian
   sudo apt install binaryen

   # macOS
   brew install binaryen
   ```

### Create Your First Web App

#### Step 1: Initialize Project

```bash
simple web init my_app
cd my_app
```

This creates:
```
my_app/
├── app.sui          # Main application file
├── README.md        # Project documentation
└── .gitignore       # Git ignore rules
```

#### Step 2: Edit `app.sui`

The generated file contains a simple counter app:

```simple
{$ let count: i32 = 0 $}

{- server -}
# Server-side code
fn get_count(): String = count.to_string()

{+ client +}
# Client-side code (compiled to WASM)
import browser.dom

fn increment():
    count = count + 1
    dom.getElementById("count").textContent = get_count()

fn decrement():
    count = count - 1
    dom.getElementById("count").textContent = get_count()

# Event bindings
dom.getElementById("inc").addEventListener("click", increment)
dom.getElementById("dec").addEventListener("click", decrement)

{@ render @}
<!DOCTYPE html>
<html>
<head>
    <title>Counter App</title>
</head>
<body>
    <h1>Counter: <span id="count">{{ get_count() }}</span></h1>
    <button id="inc">+</button>
    <button id="dec">-</button>
</body>
</html>
```

#### Step 3: Build

```bash
simple web build app.sui
```

Output:
```
public/
├── app.html              # Server-rendered HTML
├── app.wasm              # Client WASM binary
├── app.hydration.js      # Hydration script
└── app.manifest.json     # Event binding manifest
```

#### Step 4: Serve

```bash
simple web serve app.sui --port 8000 --open
```

This:
1. Builds the application
2. Starts HTTP server on port 8000
3. Opens browser automatically
4. Watches for file changes and rebuilds

Navigate to `http://localhost:8000` and interact with the counter!

---

## .sui File Format

A `.sui` file contains **four types of blocks**:

### 1. Shared State Block `{$ ... $}`

Define variables shared between server and client:

```simple
{$ let username: String = "Guest" $}
{$ let isLoggedIn: bool = false $}
{$ let items: List[String] = [] $}
```

**Rules:**
- Must come first in the file
- Variables are accessible in both server and client code
- Initial values are server-rendered, then synced to client

### 2. Server Block `{- server -} ... {- end -}`

Code that runs **only on the server** for SSR:

```simple
{- server -}
import database

fn get_users(): List[User] =
    database.query("SELECT * FROM users")

fn render_user(user: User): String =
    "<li>" + user.name + "</li>"
```

**Use cases:**
- Database queries
- API calls
- Authentication logic
- Server-side rendering functions

### 3. Client Block `{+ client +} ... {+ end +}`

Code that runs **only in the browser** (compiled to WASM):

```simple
{+ client +}
import browser.dom
import browser.fetch

fn on_button_click():
    data = await fetch.get("/api/data")
    dom.getElementById("result").textContent = data

dom.getElementById("btn").addEventListener("click", on_button_click)
```

**Use cases:**
- Event handlers
- Browser API interactions
- Client-side state updates
- Animations and effects

### 4. Template Block `{@ render @} ...`

HTML template with server-side rendering:

```simple
{@ render @}
<!DOCTYPE html>
<html>
<head>
    <title>{{ page_title }}</title>
</head>
<body>
    <h1>{{ heading }}</h1>
    {% for item in items: %}
        <li>{{ item.name }}</li>
    {% end %}
</body>
</html>
```

**Template Syntax:**
- `{{ expression }}` - Output value
- `{% for x in list: %}...{% end %}` - Loops
- `{% if condition: %}...{% end %}` - Conditionals
- `{% elif condition: %}` - Else-if
- `{% else: %}` - Else

---

## Building Web Applications

### Basic Build

```bash
simple web build app.sui
```

**Default behavior:**
- Output directory: `public/`
- Module name: derived from filename (`app.sui` → `app`)
- No optimization

### Custom Output Directory

```bash
simple web build app.sui -o dist/
```

### Custom Module Name

```bash
simple web build app.sui --module my_module
```

Output files: `my_module.html`, `my_module.wasm`, etc.

### Build with Optimization

```bash
simple web build app.sui --optimize --minify
```

**Optimizations:**
- `--optimize` - Run `wasm-opt -O3` on WASM binary (requires binaryen)
- `--minify` - Minify HTML (remove whitespace and comments)

**Size savings:**
- WASM: 20-40% reduction
- HTML: 15-25% reduction

### Production Build

```bash
simple web build app.sui -o dist/ --module app --optimize --minify
```

---

## Development Server

### Start Server

```bash
simple web serve app.sui
```

**Default options:**
- Port: 8080
- File watching: enabled
- Auto-rebuild: enabled
- Browser opening: disabled

### Custom Port

```bash
simple web serve app.sui --port 3000
```

### Disable File Watching

```bash
simple web serve app.sui --no-watch
```

Useful for production-like testing.

### Auto-Open Browser

```bash
simple web serve app.sui --open
```

Opens `http://localhost:8080` automatically.

### Combined Options

```bash
simple web serve app.sui --port 3000 --open --no-watch
```

### File Watching Behavior

When file watching is enabled:
1. Server monitors `app.sui` for changes (500ms polling interval)
2. Detects modification via file timestamp
3. Rebuilds application automatically
4. Prints rebuild notification to console

**Note:** You must **manually refresh** the browser to see changes. WebSocket live reload is planned for future releases.

---

## Hydration & Event Binding

### How Hydration Works

1. **Server renders HTML** with initial state
2. **Client loads WASM** module
3. **Hydration script** attaches event handlers to DOM
4. **Events trigger WASM** functions

### Event Binding Syntax

In client blocks, use `addEventListener`:

```simple
{+ client +}
import browser.dom

fn my_handler():
    # Handler logic
    console.log("Button clicked!")

# Bind to element by ID
dom.getElementById("btn").addEventListener("click", my_handler)

# Bind to element by class (first match)
dom.querySelector(".btn").addEventListener("click", my_handler)

# Bind to form
dom.getElementById("form").addEventListener("submit", on_submit)
```

### Supported Events

All standard DOM events are supported:

| Event Type | Examples |
|------------|----------|
| Mouse | `click`, `dblclick`, `mousedown`, `mouseup`, `mousemove` |
| Keyboard | `keydown`, `keyup`, `keypress` |
| Form | `submit`, `reset`, `change`, `input` |
| Focus | `focus`, `blur`, `focusin`, `focusout` |
| Other | `load`, `scroll`, `resize` |

### Event Options

Pass options object:

```simple
dom.getElementById("btn").addEventListener("click", handler, {
    once: true,           # Run only once
    passive: true,        # Improves scroll performance
    capture: false        # Event phase
})
```

### Hydration Manifest

The build process generates `app.manifest.json`:

```json
{
  "version": 2,
  "exports": ["increment", "decrement"],
  "bindings": [
    {
      "selector": "#inc",
      "event": "click",
      "handler": "increment",
      "options": null
    },
    {
      "selector": "#dec",
      "event": "click",
      "handler": "decrement",
      "options": null
    }
  ],
  "state": {
    "count": "0"
  },
  "metadata": {
    "generated": "2025-12-25T10:30:00Z",
    "wasm_size": 4567,
    "client_functions": 2
  }
}
```

This manifest is consumed by the hydration script to set up event bindings.

---

## Optimization

### WASM Optimization

Requires `wasm-opt` from [Binaryen](https://github.com/WebAssembly/binaryen):

```bash
simple web build app.sui --optimize
```

**What it does:**
- Runs `wasm-opt -O3` with aggressive optimization
- Strips debug information (`--strip-debug`)
- Removes producer sections (`--strip-producers`)
- Reduces binary size by 20-40%

**Optimization levels:**
- `-O1` - Basic optimization
- `-O2` - Standard optimization
- `-O3` - Aggressive optimization (used by Simple)
- `-O4` - Ultra-aggressive (may increase size for speed)

**Fallback:** If `wasm-opt` is not installed, build continues with a warning and uses unoptimized WASM.

### HTML Minification

```bash
simple web build app.sui --minify
```

**What it does:**
- Removes leading/trailing whitespace from each line
- Removes empty lines
- Strips HTML comments (`<!-- ... -->`)
- Reduces file size by 15-25%

**Limitations:**
- Does not minify inline CSS or JavaScript
- Does not optimize attribute order
- For advanced minification, use external tools

### Combined Optimization

```bash
simple web build app.sui --optimize --minify -o dist/
```

**Recommended for production builds.**

### Bundle Size Analysis

After building, check file sizes:

```bash
ls -lh dist/
```

**Typical sizes:**
- HTML: 1-5 KB (minified)
- WASM: 5-50 KB (optimized)
- Hydration JS: 1-3 KB
- Manifest JSON: <1 KB

**For large applications:**
- Use code splitting (future feature)
- Lazy-load modules
- Consider CDN hosting for static assets

---

## Best Practices

### File Organization

```
my_app/
├── app.sui              # Main app
├── components/          # Reusable components
│   ├── header.sui
│   ├── footer.sui
│   └── sidebar.sui
├── public/              # Build output (gitignored)
└── assets/              # Static assets (CSS, images)
```

### State Management

**Use shared state sparingly:**

```simple
{$ let count: i32 = 0 $}              # ✅ Good - simple primitive
{$ let users: List[User] = [] $}      # ⚠️  Be careful - large data structures
```

**For large data:** Fetch from API on client-side instead of embedding in HTML.

### Error Handling

**Client-side:**

```simple
{+ client +}
fn safe_fetch():
    try:
        data = await fetch.get("/api/data")
        # Process data
    catch e:
        console.error("Fetch failed:", e)
        dom.getElementById("error").textContent = "Failed to load data"
```

**Server-side:**

```simple
{- server -}
fn safe_render(): String =
    try:
        database.query("SELECT * FROM users")
    catch e:
        log.error("Database error:", e)
        return "<p>Error loading data</p>"
```

### Performance Tips

1. **Minimize shared state** - Large objects increase HTML size
2. **Lazy-load data** - Fetch on client-side for better initial load
3. **Use `--optimize` for production** - 20-40% WASM size reduction
4. **Cache API responses** - Use service workers (future feature)
5. **Enable compression** - Configure web server for gzip/brotli

### Security Best Practices

1. **Sanitize user input** - Always validate and escape data
2. **Use HTTPS** - Especially for production deployments
3. **Set CSP headers** - Content Security Policy in your web server
4. **Validate on server** - Never trust client-side validation alone
5. **Keep dependencies updated** - Regularly rebuild with latest compiler

### Testing

```bash
# Build and test locally
simple web build app.sui
simple web serve app.sui --port 8000

# Open browser and test
# - Check console for errors
# - Test all event handlers
# - Verify state updates

# Production build test
simple web build app.sui --optimize --minify -o dist/
cd dist && python3 -m http.server 8000
```

---

## Troubleshooting

### Build Errors

**Error: "Failed to read source file"**

```bash
error: Failed to read source file: No such file or directory
```

**Solution:** Check file path and ensure `.sui` file exists.

---

**Error: "Parser error: unexpected token"**

```bash
error: Parser error at line 10: unexpected token '{'
```

**Solution:** Check `.sui` file syntax. Ensure blocks are properly formatted:
- `{$ ... $}` for shared state
- `{- server -}` for server blocks
- `{+ client +}` for client blocks
- `{@ render @}` for templates

---

**Error: "Semantic error: undefined variable"**

```bash
error: Semantic("undefined variable: username")
```

**Solution:** Ensure variable is declared in shared state block or imported from stdlib.

---

### Optimization Errors

**Warning: "wasm-opt not found"**

```bash
warning: WASM optimization failed: wasm-opt not found
         Continuing with unoptimized binary
```

**Solution:** Install Binaryen:

```bash
# Ubuntu/Debian
sudo apt install binaryen

# macOS
brew install binaryen

# Verify installation
wasm-opt --version
```

---

**Error: "wasm-opt exited with status 1"**

```bash
warning: WASM optimization failed: wasm-opt exited with status 1
```

**Solution:** WASM binary may be corrupted. Try rebuilding without `--optimize` first, then investigate compilation errors.

---

### Server Errors

**Error: "Address already in use"**

```bash
error: Failed to bind to 0.0.0.0:8080: Address already in use
```

**Solution:** Port is in use. Either:
1. Kill the process using the port:
   ```bash
   lsof -ti:8080 | xargs kill -9
   ```

2. Use a different port:
   ```bash
   simple web serve app.sui --port 8081
   ```

---

**Error: "Permission denied"**

```bash
error: Failed to bind to 0.0.0.0:80: Permission denied
```

**Solution:** Ports < 1024 require root. Use a higher port (8000-9000) or run with sudo (not recommended).

---

### Runtime Errors

**Browser console: "Failed to fetch WASM"**

```
Failed to fetch './app.wasm': 404 Not Found
```

**Solution:** Ensure:
1. WASM file exists in public directory
2. Server is serving from correct directory
3. File permissions are correct

---

**Browser console: "WebAssembly instantiation failed"**

```
WebAssembly.instantiate() failed: Invalid binary
```

**Solution:**
1. Rebuild application
2. Check for build errors
3. Try without `--optimize` to rule out wasm-opt issues

---

**Events not firing**

**Symptoms:** Clicking buttons does nothing, no console errors.

**Solution:**
1. Open browser DevTools Console
2. Check for hydration errors
3. Verify element IDs match between HTML and client code:
   ```html
   <button id="btn">Click</button>  <!-- HTML -->
   ```
   ```simple
   dom.getElementById("btn").addEventListener(...)  # Client
   ```

4. Ensure hydration script loaded:
   ```
   View page source → Look for <script type="module">
   ```

---

## API Reference

### CLI Commands

#### `simple web build`

Build a `.sui` file into HTML, WASM, and JavaScript.

**Syntax:**
```bash
simple web build <source> [options]
```

**Arguments:**
- `<source>` - Path to `.sui` file

**Options:**
- `-o, --output <dir>` - Output directory (default: `public/`)
- `--module <name>` - Module name (default: derived from filename)
- `--optimize` - Optimize WASM with wasm-opt
- `--minify` - Minify HTML output

**Examples:**
```bash
simple web build app.sui
simple web build app.sui -o dist/
simple web build app.sui --module my_app --optimize --minify
```

---

#### `simple web serve`

Build and serve a `.sui` file with auto-rebuild.

**Syntax:**
```bash
simple web serve <source> [options]
```

**Arguments:**
- `<source>` - Path to `.sui` file

**Options:**
- `-o, --output <dir>` - Output directory (default: `public/`)
- `--module <name>` - Module name (default: derived from filename)
- `--optimize` - Optimize WASM
- `--minify` - Minify HTML
- `--port <port>` - Server port (default: 8080)
- `--no-watch` - Disable file watching
- `--open` - Open browser automatically

**Examples:**
```bash
simple web serve app.sui
simple web serve app.sui --port 3000 --open
simple web serve app.sui --optimize --minify -o dist/ --no-watch
```

---

#### `simple web init`

Initialize a new web application project.

**Syntax:**
```bash
simple web init <project_name>
```

**Arguments:**
- `<project_name>` - Name of the project directory to create

**Examples:**
```bash
simple web init my_app
cd my_app
simple web serve app.sui --open
```

---

#### `simple web features`

Display supported web framework features.

**Syntax:**
```bash
simple web features
```

**Output:**
```
Simple Web Framework - Supported Features

✅ Server-Side Rendering (SSR)
✅ WebAssembly Compilation
✅ Client-Side Hydration
✅ Event Binding (click, submit, etc.)
✅ Shared State (server ↔ client)
✅ Template Rendering
✅ Development Server
✅ File Watching & Auto-Rebuild
✅ WASM Optimization (wasm-opt)
✅ HTML Minification

📋 Coming Soon:
- WebSocket Live Reload
- Code Splitting
- Service Workers
- Progressive Web App (PWA) support
```

---

### Browser Standard Library

#### `browser.dom`

DOM manipulation module.

**Functions:**
- `getElementById(id: String): Element` - Get element by ID
- `querySelector(selector: String): Element` - Query selector
- `querySelectorAll(selector: String): List[Element]` - Query all

**Element Methods:**
- `addEventListener(event: String, handler: Function)` - Add event listener
- `addEventListener(event: String, handler: Function, options: Object)` - With options
- `textContent: String` - Get/set text content
- `innerHTML: String` - Get/set HTML content
- `setAttribute(name: String, value: String)` - Set attribute
- `getAttribute(name: String): String` - Get attribute

---

#### `browser.console`

Console logging module.

**Functions:**
- `log(...args)` - Log message
- `error(...args)` - Log error
- `warn(...args)` - Log warning
- `info(...args)` - Log info
- `debug(...args)` - Log debug message

---

#### `browser.fetch`

HTTP request module.

**Functions:**
- `get(url: String): Future[String]` - GET request
- `post(url: String, data: String): Future[String]` - POST request
- `get_json(url: String): Future[Object]` - GET JSON
- `post_json(url: String, data: Object): Future[Object]` - POST JSON

**Example:**
```simple
{+ client +}
import browser.fetch

fn load_data():
    data = await fetch.get_json("/api/users")
    # Process data...
```

---

## Examples

### Example 1: Todo List

```simple
{$ let todos: List[String] = [] $}

{- server -}
fn render_todos(): String =
    todos.map(|t| "<li>" + t + "</li>").join("")

{+ client +}
import browser.dom

fn add_todo():
    input = dom.getElementById("new-todo")
    if input.value.trim() != "":
        todos.append(input.value)
        input.value = ""
        update_todo_list()

fn update_todo_list():
    list = dom.getElementById("todo-list")
    list.innerHTML = todos.map(|t| "<li>" + t + "</li>").join("")

dom.getElementById("add-btn").addEventListener("click", add_todo)

{@ render @}
<!DOCTYPE html>
<html>
<head>
    <title>Todo List</title>
</head>
<body>
    <h1>My Todos</h1>
    <input id="new-todo" type="text" placeholder="Add a todo...">
    <button id="add-btn">Add</button>
    <ul id="todo-list">
        {{ render_todos() }}
    </ul>
</body>
</html>
```

---

### Example 2: User Authentication

```simple
{$ let isLoggedIn: bool = false $}
{$ let username: String = "" $}

{- server -}
import database

fn check_session(): bool =
    # Check server-side session
    database.has_valid_session()

isLoggedIn = check_session()

{+ client +}
import browser.dom
import browser.fetch

fn login():
    user = dom.getElementById("username").value
    pass = dom.getElementById("password").value

    result = await fetch.post_json("/api/login", {
        username: user,
        password: pass
    })

    if result.success:
        isLoggedIn = true
        username = user
        show_dashboard()
    else:
        dom.getElementById("error").textContent = "Login failed"

fn logout():
    await fetch.post("/api/logout", "")
    isLoggedIn = false
    username = ""
    show_login_form()

dom.getElementById("login-btn").addEventListener("click", login)
dom.getElementById("logout-btn").addEventListener("click", logout)

{@ render @}
<!DOCTYPE html>
<html>
<head>
    <title>User Auth</title>
</head>
<body>
    {% if isLoggedIn: %}
        <h1>Welcome, {{ username }}!</h1>
        <button id="logout-btn">Logout</button>
    {% else: %}
        <h1>Login</h1>
        <input id="username" type="text" placeholder="Username">
        <input id="password" type="password" placeholder="Password">
        <button id="login-btn">Login</button>
        <div id="error"></div>
    {% end %}
</body>
</html>
```

---

### Example 3: Real-Time Dashboard

```simple
{$ let metrics: Object = {cpu: 0, memory: 0, disk: 0} $}

{- server -}
import monitoring

metrics = monitoring.get_current_metrics()

{+ client +}
import browser.fetch
import browser.dom

fn update_metrics():
    while true:
        data = await fetch.get_json("/api/metrics")

        dom.getElementById("cpu").textContent = data.cpu.to_string() + "%"
        dom.getElementById("memory").textContent = data.memory.to_string() + "MB"
        dom.getElementById("disk").textContent = data.disk.to_string() + "GB"

        await sleep(5000)  # Update every 5 seconds

# Start updating on page load
update_metrics()

{@ render @}
<!DOCTYPE html>
<html>
<head>
    <title>System Dashboard</title>
    <style>
        .metric { font-size: 2em; margin: 20px; }
        .label { color: #666; }
    </style>
</head>
<body>
    <h1>System Metrics</h1>
    <div class="metric">
        <span class="label">CPU:</span>
        <span id="cpu">{{ metrics.cpu }}</span>%
    </div>
    <div class="metric">
        <span class="label">Memory:</span>
        <span id="memory">{{ metrics.memory }}</span>MB
    </div>
    <div class="metric">
        <span class="label">Disk:</span>
        <span id="disk">{{ metrics.disk }}</span>GB
    </div>
</body>
</html>
```

---

## Conclusion

The Simple Web Framework provides a **modern, type-safe** way to build web applications with **server-side rendering** and **client-side interactivity**. The unified `.sui` file format keeps your code organized and maintainable.

**Next Steps:**
1. Create your first app with `simple web init my_app`
2. Experiment with the examples above
3. Read the [API Reference](#api-reference) for detailed documentation
4. Join the community at https://github.com/simple-lang/simple

**Resources:**
- [Simple Language Documentation](../spec/language.md)
- [Standard Library Reference](../spec/stdlib.md)
- [WebAssembly Guide](../research/wasm_plan.md)
- [GitHub Repository](https://github.com/simple-lang/simple)

Happy coding! 🚀
