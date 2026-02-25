# Simple UI Framework Specification

Unified `.sui` files with server/client execution model, dual renderer (GUI + TUI), and shared state architecture.

---

## 1. Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    Unified .sui Model                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│                      Shared State                               │
│                    {$ let x: T $}                               │
│                          │                                      │
│           ┌──────────────┼──────────────┐                       │
│           ▼              │              ▼                       │
│    ┌────────────┐        │       ┌────────────┐                 │
│    │   SERVER   │        │       │   CLIENT   │                 │
│    │   {- -}    │        │       │   {+ +}    │                 │
│    │            │        │       │            │                 │
│    │ • DB query │        │       │ • Events   │                 │
│    │ • Session  │        │       │ • Fetch    │                 │
│    │ • Auth     │        │       │ • DOM ops  │                 │
│    └─────┬──────┘        │       └─────┬──────┘                 │
│          │               │             │                        │
│          └───────────────┼─────────────┘                        │
│                          ▼                                      │
│              ┌───────────────────────┐                          │
│              │    Render Template    │                          │
│              │  {{ expr }}  {% %}    │                          │
│              └───────────┬───────────┘                          │
│                          │                                      │
│              ┌───────────┴───────────┐                          │
│              ▼                       ▼                          │
│         HTML String              PatchSet                       │
│         (SSR output)          (client updates)                  │
│              │                       │                          │
│              ▼                       ▼                          │
│    ┌─────────────────┐     ┌─────────────────┐                  │
│    │   GUI Renderer  │     │   TUI Renderer  │                  │
│    │   (DOM/WebView) │     │   (Terminal)    │                  │
│    └─────────────────┘     └─────────────────┘                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Key Insight**: State is declared once, but initialized/updated at different times:
- **Server** (`{- -}`): Sets initial values (DB, session, auth)
- **Client** (`{+ +}`): Updates on user interaction (events, fetch)
- **Render** (`{{ }}`, `{% %}`): Reads state, outputs HTML or patches

---

## 2. Template Syntax

All syntax uses `{` prefix with distinct second character:

| Syntax | Name | Purpose | Runs on |
|--------|------|---------|---------|
| `{@ ... @}` | Directive | Component/page declaration, embed | Compile-time |
| `{$ ... $}` | Declaration | State fields (shared) | Compile-time |
| `{- ... -}` | Server block | Initial data, DB, session | Server only |
| `{+ ... +}` | Client block | Events, fetch, DOM | Client only |
| `{{ expr }}` | Output | HTML-escaped expression | Both |
| `{! expr !}` | Raw output | Unescaped (unsafe) | Both |
| `{% ... %}` | Render code | if/for/let statements | Both |
| `{# ... #}` | Comment | Ignored | Neither |

### Example: Counter Component

**UI File**: `app/ui/components/Counter.ui.sui`
```html
{@ component Counter @}

{$ let count: i32 $}

{- count = props.start or 0 -}

{+
  on_click("#inc", fn(): count += 1)
  on_click("#dec", fn(): count -= 1)
+}

<div class="counter">
  <button id="dec">-</button>
  <span>{{ count }}</span>
  <button id="inc">+</button>
</div>
```

**Logic File**: `app/logic/components/Counter.spl`
```spl
class Counter:
    fn reset():
        this.count = 0
        invalidate()
```

---

## 3. Execution Timeline

```
REQUEST LIFECYCLE
─────────────────

1. Request arrives at server
        │
        ▼
2. Parse .sui, execute {- server -} block
   ┌─────────────────────────────────────┐
   │ {- users = db.query("SELECT...") -} │
   │ {- session = get_session(req)     -} │
   └─────────────────────────────────────┘
        │
        ▼
3. Render template → HTML string
   ┌─────────────────────────────────────┐
   │ {{ users.len() }} users found       │
   │ {% for u in users: %}               │
   │   <li>{{ u.name }}</li>             │
   │ {% end %}                           │
   └─────────────────────────────────────┘
        │
        ▼
4. Send HTML to browser
        │
        ════════════════════════════════════
        │
        ▼
5. Browser displays static HTML
        │
        ▼
6. Load WASM module
        │
        ▼
7. Hydrate: execute {+ client +} block
   ┌─────────────────────────────────────┐
   │ {+ on_click("#btn", handler)      +} │
   │ {+ on_input("#search", filter)    +} │
   └─────────────────────────────────────┘
        │
        ▼
8. User interacts (click, type, etc.)
        │
        ▼
9. Event handler updates state
        │
        ▼
10. Re-render → PatchSet (not full HTML)
        │
        ▼
11. Apply patches to DOM/TUI
```

---

## 4. File Types and Structure

### 4.1 Page vs Component

| Type | Extension | Purpose |
|------|-----------|---------|
| Page | `.page.sui` | Root mount point, routing, SSR entry |
| Component | `.ui.sui` | Reusable embedded component |

### 4.2 Directory Layout

```
app/
  ui/
    pages/
      Home.page.sui        # SSR entry point
      Users.page.sui
    components/
      Counter.ui.sui       # Reusable component
      UserList.ui.sui
    layouts/
      AppShell.ui.sui      # Layout wrapper
  logic/
    pages/
      Home.spl             # Page logic
      Users.spl
    components/
      Counter.spl          # Component logic
      UserList.spl
    layouts/
      AppShell.spl
  assets/
    styles/
      base.css             # GUI styles
      theme.tui.toml       # TUI theme mapping
```

### 4.3 UI/Logic Pairing Rules

For every `.sui` file, a matching `.spl` file must exist:

```
app/ui/components/Counter.ui.sui
      ↕ (paired)
app/logic/components/Counter.spl  →  class Counter { ... }
```

---

## 5. Embedding Components

Use `{@ embed @}` to include components:

```html
{@ page Home @}

{$ let users: List[User] $}

{- users = UserService.list() -}

<main>
  <h1>Welcome</h1>

  {# Embed component with props #}
  {@ embed UserList users=users @}

  {# Embed with hydration strategy #}
  {@ embed SearchBox query="" hydrate="visible" @}
</main>
```

### Hydration Strategies

| Strategy | When hydrates |
|----------|---------------|
| `hydrate="load"` | Immediately on page load (default) |
| `hydrate="visible"` | When scrolled into viewport |
| `hydrate="idle"` | During browser idle time |
| `hydrate="interaction"` | On first user interaction |
| `hydrate="none"` | Never (static only) |

---

## 6. Control Flow in Templates

### Conditionals

```html
{% if user.is_admin: %}
  <button>Delete All</button>
{% elif user.is_mod: %}
  <button>Moderate</button>
{% else: %}
  <span>Read only</span>
{% end %}
```

### Loops

```html
<ul>
  {% for item in items: %}
    <li key="{{ item.id }}">{{ item.name }}</li>
  {% end %}
</ul>
```

### Local Variables

```html
{% let total = items.map(i => i.price).sum() %}
<span>Total: {{ total }}</span>
```

---

## 7. Server vs Client Code

### 7.1 Server Block (`{- -}`)

Runs **once** during SSR. Has access to:
- Database connections
- Session/auth data
- File system
- Environment variables

```html
{-
  let session = get_session(request)
  let user = db.find_user(session.user_id)
  let posts = db.query("SELECT * FROM posts WHERE author = ?", user.id)
-}
```

### 7.2 Client Block (`{+ +}`)

Runs **after hydration** in browser. Has access to:
- DOM events
- Fetch API
- Local storage
- Browser APIs

```html
{+
  on_click("#load-more", async fn():
    let more = await fetch_json("/api/posts?page=" + page)
    posts = posts.concat(more)
    invalidate()
  )

  on_input("#search", fn(e):
    filter = e.target.value
    invalidate()
  )
+}
```

### 7.3 What Goes Where?

| Code Type | Server `{- -}` | Client `{+ +}` |
|-----------|----------------|----------------|
| DB queries | ✓ | ✗ (use fetch) |
| Session access | ✓ | ✗ |
| File I/O | ✓ | ✗ |
| Event handlers | ✗ | ✓ |
| DOM manipulation | ✗ | ✓ |
| Fetch API | ✗ | ✓ |
| Initial state | ✓ | restore from SSR |

---

## 8. Layouts and Slots

### 8.1 Defining a Layout

```html
{@ layout AppShell @}

{$ let title: str $}

<html>
  <head>
    <title>{{ title }} - MyApp</title>
  </head>
  <body>
    <nav>{@ slot nav @}</nav>
    <main>{@ slot main @}</main>
    <footer>&copy; 2025</footer>
  </body>
</html>
```

### 8.2 Using a Layout

```html
{@ page Home layout=AppShell title="Home" @}

{@ fill nav @}
  <a href="/">Home</a>
  <a href="/about">About</a>
{@ end @}

{@ fill main @}
  <h1>Welcome!</h1>
  <p>Content here...</p>
{@ end @}
```

---

## 9. Dual Renderer: GUI + TUI

Same `.sui` compiles to both:

### 9.1 GUI (Browser/WebView)

- Outputs real HTML/CSS
- Uses DOM for updates
- Full CSS support

### 9.2 TUI (Terminal)

- Outputs to terminal buffer
- Uses box-drawing, colors
- Subset of CSS (flex, padding, margin)
- Keyboard navigation

### 9.3 Element Mapping

| Sui Element | GUI | TUI |
|-------------|-----|-----|
| `<div>` | `<div>` | Box |
| `<span>` | `<span>` | Inline text |
| `<button>` | `<button>` | `[ Label ]` |
| `<input>` | `<input>` | `[________]` |
| `<ul>/<li>` | List | Bulleted lines |
| `<table>` | Table | ASCII table |

### 9.4 TUI Theme

```toml
# theme.tui.toml
[colors]
primary = "blue"
danger = "red"
text = "white"
bg = "black"

[borders]
default = "single"  # single, double, rounded, none

[focus]
style = "reverse"
```

---

## 10. PatchSet Architecture

Render produces patches, not full re-renders:

```
┌─────────────────────────────────────────┐
│              PatchSet                   │
├─────────────────────────────────────────┤
│ SetText(nodeId, text)                   │
│ SetAttr(nodeId, name, value)            │
│ AddClass(nodeId, class)                 │
│ RemoveClass(nodeId, class)              │
│ InsertChild(parentId, index, subtree)   │
│ RemoveChild(parentId, childId)          │
│ ReplaceSubtree(nodeId, subtree)         │
│ MoveChild(parentId, fromIdx, toIdx)     │
└─────────────────────────────────────────┘
```

---

## 11. Runtime APIs

### 11.1 Client APIs (in `{+ +}` blocks)

```spl
# Events
on_click(selector, handler)
on_input(selector, handler)
on_key(selector, key, handler)
on_submit(selector, handler)

# State
invalidate()                    # Request re-render
schedule_render(delay_ms)       # Delayed render

# Navigation
navigate(path)                  # Client-side nav
navigate(path, replace=true)    # Replace history

# Context
provide(key, value)             # Set context for children
use(key) -> T                   # Get context value

# Storage
local_get(key) -> str?
local_set(key, value)
session_get(key) -> str?
session_set(key, value)
```

### 11.2 Server APIs (in `{- -}` blocks)

```spl
# Request
get_session(req) -> Session
get_cookie(req, name) -> str?
get_header(req, name) -> str?

# Response helpers
redirect(url)
set_cookie(name, value, opts)
set_header(name, value)
```

---

## 12. Milestones

| Phase | Features | Difficulty |
|-------|----------|------------|
| M0 | Parser, IR design, pairing rules | Medium |
| M1 | Static templates, `{{ }}` holes | Medium |
| M2 | `{- -}` / `{+ +}` blocks, events | High |
| M3 | Binding graph, reactivity | High |
| M4 | TUI renderer | High |
| M5 | `{% if %}` / `{% for %}` | Very High |
| M6 | SSR + hydration | Very High |

---

## 13. Full Example: User List Page

**Page**: `app/ui/pages/Users.page.sui`
```html
{@ page Users layout=AppShell title="Users" @}

{$ let users: List[User] $}
{$ let filter: str $}
{$ let loading: bool $}

{-
  users = db.query("SELECT * FROM users ORDER BY name")
  filter = ""
  loading = false
-}

{+
  on_input("#search", fn(e):
    filter = e.target.value
    invalidate()
  )

  on_click("#refresh", async fn():
    loading = true
    invalidate()
    users = await fetch_json("/api/users")
    loading = false
    invalidate()
  )
+}

{@ fill main @}
  <div class="toolbar">
    <input id="search" placeholder="Filter..." value="{{ filter }}" />
    <button id="refresh">
      {% if loading: %}Loading...{% else: %}Refresh{% end %}
    </button>
  </div>

  <ul class="user-list">
    {% for u in users.filter(u => u.name.contains(filter)): %}
      <li key="{{ u.id }}">
        <strong>{{ u.name }}</strong>
        <span>{{ u.email }}</span>
      </li>
    {% end %}
  </ul>
{@ end @}
```

**Logic**: `app/logic/pages/Users.spl`
```spl
class Users:
    fn delete_user(id: i64):
        this.users = this.users.filter(u => u.id != id)
        invalidate()
```

---

## 14. See Also

- `doc/web_framework.md` - Routing, controllers, API endpoints
- `doc/feature.md` - Feature list (#500-536)
- `doc/spec/language.md` - Simple language specification
