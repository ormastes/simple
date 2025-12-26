# Simple Web Framework - Quick Reference

**Version:** 1.0 | **Date:** 2025-12-25

## 30-Second Quickstart

```bash
# Create new app
simple web init my_app && cd my_app

# Start development server
simple web serve app.sui --open

# Build for production
simple web build app.sui --optimize --minify -o dist/
```

---

## .sui File Structure

```simple
{$ let state: Type = value $}        # Shared state (optional)

{- server -}                          # Server-side code
fn render(): String = "HTML"

{+ client +}                          # Client-side code (WASM)
import browser.dom
fn handler(): ...
dom.getElementById("id").addEventListener("event", handler)

{@ render @}                          # HTML template
<!DOCTYPE html>
<html>...</html>
```

---

## CLI Commands

| Command | Description | Example |
|---------|-------------|---------|
| `web build <file>` | Build to HTML+WASM | `simple web build app.sui` |
| `web serve <file>` | Dev server + watch | `simple web serve app.sui --open` |
| `web init <name>` | Create new project | `simple web init my_app` |
| `web features` | List features | `simple web features` |

### Build Options

| Flag | Description | Default |
|------|-------------|---------|
| `-o, --output <dir>` | Output directory | `public/` |
| `--module <name>` | Module name | From filename |
| `--optimize` | Run wasm-opt | Off |
| `--minify` | Minify HTML | Off |

### Serve Options

| Flag | Description | Default |
|------|-------------|---------|
| `--port <port>` | Server port | `8080` |
| `--no-watch` | Disable auto-rebuild | Watch enabled |
| `--open` | Open browser | Don't open |

---

## Event Binding

```simple
{+ client +}
import browser.dom

# By ID
dom.getElementById("btn").addEventListener("click", handler)

# By selector
dom.querySelector(".btn").addEventListener("click", handler)

# With options
dom.getElementById("btn").addEventListener("click", handler, {
    once: true,
    passive: true
})
```

---

## Template Syntax

```html
{@ render @}
<!-- Variables -->
{{ variable }}

<!-- Conditionals -->
{% if condition: %}
    <p>True</p>
{% elif other: %}
    <p>Else if</p>
{% else: %}
    <p>False</p>
{% end %}

<!-- Loops -->
{% for item in list: %}
    <li>{{ item.name }}</li>
{% end %}
```

---

## Browser APIs

### DOM

```simple
import browser.dom

# Query
elem = dom.getElementById("id")
elem = dom.querySelector(".class")
elems = dom.querySelectorAll("div")

# Modify
elem.textContent = "New text"
elem.innerHTML = "<b>Bold</b>"
elem.setAttribute("class", "active")
value = elem.getAttribute("data-id")
```

### Console

```simple
import browser.console

console.log("Message", value)
console.error("Error:", err)
console.warn("Warning")
console.info("Info")
console.debug("Debug info")
```

### Fetch

```simple
import browser.fetch

# GET
data = await fetch.get("/api/data")
json = await fetch.get_json("/api/users")

# POST
result = await fetch.post("/api/submit", body)
result = await fetch.post_json("/api/create", {name: "John"})
```

---

## Common Patterns

### Counter

```simple
{$ let count: i32 = 0 $}

{+ client +}
import browser.dom

fn increment():
    count += 1
    dom.getElementById("count").textContent = count.to_string()

dom.getElementById("btn").addEventListener("click", increment)

{@ render @}
<h1>Count: <span id="count">{{ count }}</span></h1>
<button id="btn">+</button>
```

### Form Handling

```simple
{+ client +}
import browser.dom

fn on_submit(event):
    event.preventDefault()

    name = dom.getElementById("name").value
    email = dom.getElementById("email").value

    # Process form...
    console.log("Submitted:", name, email)

dom.getElementById("form").addEventListener("submit", on_submit)

{@ render @}
<form id="form">
    <input id="name" type="text" required>
    <input id="email" type="email" required>
    <button type="submit">Submit</button>
</form>
```

### API Integration

```simple
{+ client +}
import browser.fetch
import browser.dom

fn load_data():
    try:
        data = await fetch.get_json("/api/users")
        display_users(data)
    catch e:
        dom.getElementById("error").textContent = "Failed to load"

fn display_users(users):
    html = users.map(|u| "<li>" + u.name + "</li>").join("")
    dom.getElementById("users").innerHTML = html

load_data()  # Load on page init

{@ render @}
<ul id="users"></ul>
<div id="error"></div>
```

---

## Optimization

### Development Build

```bash
simple web build app.sui
```

**Output:**
- HTML: ~5 KB
- WASM: ~50 KB (unoptimized)

### Production Build

```bash
simple web build app.sui --optimize --minify -o dist/
```

**Output:**
- HTML: ~3 KB (40% smaller)
- WASM: ~30 KB (40% smaller)

**Requirements:**
- Install `binaryen` for wasm-opt:
  ```bash
  # Ubuntu/Debian
  sudo apt install binaryen

  # macOS
  brew install binaryen
  ```

---

## File Structure

### Generated Project

```
my_app/
├── app.sui              # Source file
├── public/              # Build output (gitignored)
│   ├── app.html
│   ├── app.wasm
│   ├── app.hydration.js
│   └── app.manifest.json
├── README.md
└── .gitignore
```

### Build Outputs

| File | Description | Size |
|------|-------------|------|
| `app.html` | Server-rendered HTML + loader | 1-5 KB |
| `app.wasm` | Client-side WASM binary | 5-50 KB |
| `app.hydration.js` | Event binding script | 1-3 KB |
| `app.manifest.json` | Hydration manifest | <1 KB |

---

## Troubleshooting

### Build Fails

```bash
# Check syntax
simple web build app.sui

# Common issues:
# - Missing closing tags in blocks
# - Undefined variables
# - Import errors
```

### Server Won't Start

```bash
# Port in use
simple web serve app.sui --port 8081

# Permission denied (port < 1024)
simple web serve app.sui --port 8080
```

### Events Not Working

1. Check browser console (F12)
2. Verify element IDs match
3. Ensure hydration script loaded (view page source)

### WASM Optimization Failed

```bash
# Install wasm-opt
sudo apt install binaryen     # Ubuntu/Debian
brew install binaryen         # macOS

# Verify
wasm-opt --version
```

---

## Best Practices

✅ **DO:**
- Use shared state for simple primitives
- Handle errors in client code
- Test locally before deploying
- Optimize for production builds
- Version control your `.sui` files

❌ **DON'T:**
- Embed large data in shared state
- Trust client-side validation alone
- Commit `public/` directory
- Use ports < 1024
- Ignore console warnings

---

## Next Steps

1. **Read full guide:** [WEB_FRAMEWORK_GUIDE.md](WEB_FRAMEWORK_GUIDE.md)
2. **Explore examples:** See guide for todo list, auth, dashboard
3. **Join community:** https://github.com/simple-lang/simple
4. **Report issues:** https://github.com/simple-lang/simple/issues

---

## Resources

- [Language Spec](spec/language.md)
- [Standard Library](spec/stdlib.md)
- [API Reference](WEB_FRAMEWORK_GUIDE.md#api-reference)
- [GitHub](https://github.com/simple-lang/simple)

**Happy coding!** 🚀
