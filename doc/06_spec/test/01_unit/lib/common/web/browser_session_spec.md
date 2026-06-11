# Browser Session Specification

> 1. var session = BrowserSession new

<!-- sdn-diagram:id=browser_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Specification

## Scenarios

### BrowserSession lifecycle

#### opens about blank

1. var session = BrowserSession new

2. Ok
   - Expected: session.current_url equals `about:blank`
   - Expected: session.current_title equals `about:blank`
   - Expected: session.history.len() equals `1`

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_url("about:blank")
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:blank")
        expect(session.current_title).to_equal("about:blank")
        expect(session.history.len()).to_equal(1)
    Err(e) =>
        fail("Expected about:blank navigation to succeed: {e}")
```

</details>

#### stops pending navigation before commit

1. var session = BrowserSession new

2. session begin navigation

3. session stop loading

4. Ok

5. fail

6. Err
   - Expected: e equals `no pending navigation`
   - Expected: session.history.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.begin_navigation("about:pending")
session.stop_loading()
val result = session.commit_navigation_html("<html><body>ignored</body></html>")
match result:
    Ok(_) =>
        fail("Expected stopped pending navigation to reject commit")
    Err(e) =>
        expect(e).to_equal("no pending navigation")
        expect(session.history.len()).to_equal(0)
```

</details>

#### rejects network navigation honestly

1. var session = BrowserSession new

2. Ok

3. fail

4. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_url("https://example.com")
match result:
    Ok(_) =>
        fail("Expected network navigation to remain explicitly unimplemented")
    Err(e) =>
        expect(e).to_contain("network navigation is not implemented")
```

</details>

### BrowserSession page loading

#### extracts title and body from html

1. var session = BrowserSession new

2. Ok
   - Expected: session.current_url equals `about:test`
   - Expected: session.current_title equals `Test Page`
   - Expected: session.history.len() equals `1`

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:test",
    "<!DOCTYPE html><html><head><title>Test Page</title></head><body><h1>Hello</h1></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:test")
        expect(session.current_title).to_equal("Test Page")
        expect(session.current_body_html).to_contain("<h1>Hello</h1>")
        expect(session.history.len()).to_equal(1)
    Err(e) =>
        fail("Expected HTML title/body extraction to succeed: {e}")
```

</details>

#### runs inline scripts against document and body

1. var session = BrowserSession new

2. Ok
   - Expected: session.current_title equals `After`
   - Expected: session.warnings.len() equals `0`

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:scripted",
    "<html><head><title>Before</title></head><body><p>Old</p><script>document.title = 'After'; document.body.innerHTML = '<section>New</section>';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("After")
        expect(session.current_body_html).to_contain("<section>New</section>")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected inline document/body script execution to succeed: {e}")
```

</details>

#### runs zero-delay timer callbacks after inline scripts

1. var session = BrowserSession new

2. "<html><head><title>Before</title></head><body><p>Old</p><script>setTimeout

3. Ok
   - Expected: session.current_title equals `Timer`
   - Expected: session.current_body_html equals `Done`
   - Expected: session.warnings.len() equals `0`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:timer",
    "<html><head><title>Before</title></head><body><p>Old</p><script>setTimeout(function(){ document.title = 'Timer'; document.body.textContent = 'Done'; }, 0);</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Timer")
        expect(session.current_body_html).to_equal("Done")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected zero-delay timer callbacks to run after inline scripts: {e}")
```

</details>

#### loads registered external scripts in source order

1. var session = BrowserSession new

2. session register resource

3. Ok
   - Expected: session.current_title equals `Loaded`
   - Expected: session.warnings.len() equals `0`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/app.js", "document.body.innerHTML = '<h2>External</h2>'; document.title = 'Loaded';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Before</title><script src='/app.js'></script></head><body><p>Old</p></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Loaded")
        expect(session.current_body_html).to_contain("<h2>External</h2>")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected registered external scripts to load in source order: {e}")
```

</details>

#### preserves inline style blocks in the rendered session document

1. var session = BrowserSession new

2. Ok
   - Expected: session.warnings.len() equals `0`

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:styles",
    "<html><head><style>body { color: red; }</style></head><body>styled</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_contain("body { color: red; }")
        expect(session.render_html_document()).to_contain("<style>body { color: red; }</style>")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected inline style blocks to remain in rendered session document: {e}")
```

</details>

#### loads linked stylesheets through the session request pump

1. var session = BrowserSession new

2. session register resource

3. Ok
   - Expected: session.warnings.len() equals `0`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/site.css", "body { background: rgb(1, 2, 3); }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><link rel='stylesheet' href='/site.css'></head><body>styled</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_contain("background: rgb(1, 2, 3);")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected linked stylesheet resource to load through the session pump: {e}")
```

</details>

#### expands stylesheet imports before rendering

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/base.css", "@import '/theme.css'; body { color: red; }")
session.register_resource("https://example.com/theme.css", ".theme { background: blue; }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><link rel='stylesheet' href='/base.css'></head><body class='theme'>styled</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_contain(".theme { background: blue; }")
        expect(session.current_style_html).to_contain("body { color: red; }")
    Err(e) =>
        fail("Expected stylesheet imports to expand before rendering: {e}")
```

</details>

#### loads external module graphs with named imports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_title equals `ModuleLoaded`
   - Expected: session.current_body_html equals `dep`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const label = 'dep';")
session.register_resource("https://example.com/module.js", "import \{ label \} from '/dep.js'; document.title = 'ModuleLoaded'; document.body.textContent = label;")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Before</title><script type='module' src='/module.js' defer></script></head><body>start</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("ModuleLoaded")
        expect(session.current_body_html).to_equal("dep")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected external module graph with named imports to load: {e}")
```

</details>

#### supports inline module default and namespace imports

1. var session = BrowserSession new

2. session register resource

3. "<html><body><script type='module'>import greet, * as lib from '/lib js'; document body textContent = greet

4. Ok
   - Expected: session.current_body_html equals `hi browser!`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/lib.js", "export default function greet(name) { return 'hi ' + name; } export const suffix = '!';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import greet, * as lib from '/lib.js'; document.body.textContent = greet('browser') + lib.suffix;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("hi browser!")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected inline module default and namespace imports to load: {e}")
```

</details>

#### supports module default class exports and named re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. "<html><body><script type='module'>import Bridge, \{ bridged \} from '/bridge js'; document body textContent =

5. Ok
   - Expected: session.current_body_html equals `Bridge:v`
   - Expected: session.warnings.len() equals `0`

6. Err

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const value = 'v';")
session.register_resource("https://example.com/bridge.js", "export \{ value as bridged \} from '/dep.js'; export default class Bridge { constructor() { this.kind = 'Bridge'; } }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import Bridge, \{ bridged \} from '/bridge.js'; document.body.textContent = (new Bridge()).kind + ':' + bridged;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("Bridge:v")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected module default class export and named re-export to load: {e}")
```

</details>

#### supports anonymous default function and class exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. "<html><body><script type='module'>import anonFn from '/anon-fn js'; import AnonClass from '/anon-class js'; document body textContent = anonFn

5. Ok
   - Expected: session.current_body_html equals `anon module:Anon`
   - Expected: session.warnings.len() equals `0`

6. Err

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/anon-fn.js", "export default function(name) { return 'anon ' + name; }")
session.register_resource("https://example.com/anon-class.js", "export default class { constructor() { this.kind = 'Anon'; } }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import anonFn from '/anon-fn.js'; import AnonClass from '/anon-class.js'; document.body.textContent = anonFn('module') + ':' + (new AnonClass()).kind;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("anon module:Anon")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected anonymous default function and class exports to load: {e}")
```

</details>

#### supports export star re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `A:B`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const a = 'A'; export const b = 'B';")
session.register_resource("https://example.com/bridge.js", "export * from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import { a, b } from '/bridge.js'; document.body.textContent = a + ':' + b;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("A:B")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star re-exports to load: {e}")
```

</details>

#### does not forward default through export star re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `N`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export * from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ named \} from '/bridge.js'; document.body.textContent = named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star re-export to omit default forwarding: {e}")
```

</details>

#### keeps explicit local exports ahead of export star re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `bridge`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const value = 'dep';")
session.register_resource("https://example.com/bridge.js", "export const value = 'bridge'; export * from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ value \} from '/bridge.js'; document.body.textContent = value;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("bridge")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected explicit local exports to take precedence over export star: {e}")
```

</details>

#### supports export star as namespace re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `dep:x`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const value = 'dep'; export const other = 'x';")
session.register_resource("https://example.com/bridge.js", "export * as ns from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import { ns } from '/bridge.js'; document.body.textContent = ns.value + ':' + ns.other;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("dep:x")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star namespace re-export to load: {e}")
```

</details>

#### supports multi-declarator variable exports from a single module statement

1. var session = BrowserSession new

2. session register resource

3. Ok
   - Expected: session.current_body_html equals `A:B:C:D`
   - Expected: session.warnings.len() equals `0`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const a = 'A', b = 'B'; export let c = 'C', d = 'D';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import { a, b, c, d } from '/dep.js'; document.body.textContent = a + ':' + b + ':' + c + ':' + d;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("A:B:C:D")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected multi-declarator variable exports to load: {e}")
```

</details>

#### keeps default on export star as namespace re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export * as ns from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ ns \} from '/bridge.js'; document.body.textContent = ns.default + ':' + ns.named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star namespace re-export to keep default: {e}")
```

</details>

#### supports default re-export aliases from dependency modules

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export \{ default as depDefault, named \} from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ depDefault, named \} from '/bridge.js'; document.body.textContent = depDefault + ':' + named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected default re-export aliases from dependency modules to load: {e}")
```

</details>

#### keeps default on export star as namespace re-exports

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export * as ns from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ ns \} from '/bridge.js'; document.body.textContent = ns.default + ':' + ns.named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected repeated export star namespace re-export to keep default: {e}")
```

</details>

#### supports default re-export aliases from dependency modules

1. var session = BrowserSession new

2. session register resource

3. session register resource

4. Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export \{ default as depDefault, named \} from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ depDefault, named \} from '/bridge.js'; document.body.textContent = depDefault + ':' + named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected repeated default re-export alias case to load: {e}")
```

</details>

#### runs async classic scripts after parser-blocking inline scripts

1. var session = BrowserSession new

2. session register resource

3. Ok
   - Expected: session.current_title equals `Start:inline:async`
   - Expected: session.warnings.len() equals `0`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/async.js", "document.title = document.title + ':async';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Start</title></head><body><script async src='/async.js'></script><script>document.title = document.title + ':inline';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Start:inline:async")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected async classic script to run after parser-blocking inline script: {e}")
```

</details>

#### runs defer classic scripts after parser-blocking inline scripts

1. var session = BrowserSession new

2. session register resource

3. Ok
   - Expected: session.current_title equals `Start:inline:defer`
   - Expected: session.warnings.len() equals `0`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/defer.js", "document.title = document.title + ':defer';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Start</title><script defer src='/defer.js'></script></head><body><script>document.title = document.title + ':inline';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Start:inline:defer")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected defer classic script to run after parser-blocking inline script: {e}")
```

</details>

#### supports deterministic document loading without the js runtime

1. var session = BrowserSession new without runtime

2. Ok
   - Expected: session.current_url equals `about:deterministic`
   - Expected: session.current_title equals `Deterministic`
   - Expected: session.warnings.len() equals `1`

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new_without_runtime()
val result = session.open_html(
    "about:deterministic",
    "<html><head><title>Deterministic</title></head><body><p>Stable</p><script>document.title = 'Ignored';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:deterministic")
        expect(session.current_title).to_equal("Deterministic")
        expect(session.current_body_html).to_contain("<p>Stable</p>")
        expect(session.runtime_state).to_be_nil()
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("runtime is disabled")
    Err(e) =>
        fail("Expected deterministic no-runtime document loading to succeed: {e}")
```

</details>

### BrowserSession script bridge

#### exposes browser like globals

1. var session = BrowserSession new

2. session open html

3. Ok

4. Err

5. fail

6. Ok
   - Expected: _display_js(value) equals `about:globals`

7. Err

8. fail

9. Ok
   - Expected: _display_js(value) equals `true`

10. Err

11. fail

12. Ok
   - Expected: _display_js(value) equals `true`

13. Err

14. fail

15. Ok
   - Expected: _display_js(value) equals `complete`

16. Err

17. fail

18. Ok
   - Expected: _display_js(value) equals `about:globals`

19. Err

20. fail

21. Ok
   - Expected: _display_js(value) equals `about:globals`

22. Err

23. fail

24. Ok
   - Expected: _display_js(value) equals `expected_platform`

25. Err

26. fail

27. Ok

28. Err

29. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:globals", "<html><body><p>Hi</p></body></html>")

val ua_result = session.eval_script("navigator.userAgent")
match ua_result:
    Ok(value) =>
        expect(_display_js(value)).to_contain("Chrome/")
    Err(e) =>
        fail("Expected navigator.userAgent to evaluate: {e}")

val href_result = session.eval_script("window.location.href")
match href_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("about:globals")
    Err(e) =>
        fail("Expected window.location.href to evaluate: {e}")

val self_result = session.eval_script("window.self === window")
match self_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true")
    Err(e) =>
        fail("Expected window.self identity check to evaluate: {e}")

val body_result = session.eval_script("document.body !== null")
match body_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true")
    Err(e) =>
        fail("Expected document.body presence check to evaluate: {e}")

val ready_result = session.eval_script("document.readyState")
match ready_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("complete")
    Err(e) =>
        fail("Expected document.readyState to evaluate: {e}")

val path_result = session.eval_script("window.location.pathname")
match path_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("about:globals")
    Err(e) =>
        fail("Expected window.location.pathname to evaluate: {e}")

val url_result = session.eval_script("document.URL")
match url_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("about:globals")
    Err(e) =>
        fail("Expected document.URL to evaluate: {e}")

val platform_result = session.eval_script("navigator.platform")
val expected_platform = _expected_navigator_platform()
match platform_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal(expected_platform)
    Err(e) =>
        fail("Expected navigator.platform to evaluate: {e}")

val platform_ua_token = _expected_user_agent_token()
if platform_ua_token.len() > 0:
    match ua_result:
        Ok(value) =>
            expect(_display_js(value)).to_contain(platform_ua_token)
        Err(e) =>
            fail("Expected navigator.userAgent platform token check to reuse evaluated user agent: {e}")
```

</details>

#### exposes complete location URL parts

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `https:|example.com:8443|https://example.com:8443|/path/page|?q=1|#top`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com:8443/path/page?q=1#top", "<html><body>URL</body></html>")

val result = session.eval_script("location.protocol + '|' + location.host + '|' + location.origin + '|' + location.pathname + '|' + location.search + '|' + location.hash")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https:|example.com:8443|https://example.com:8443|/path/page|?q=1|#top")
    Err(e) =>
        fail("Expected complete location URL parts to evaluate: {e}")
```

</details>

#### keeps location parts coherent after href mutation

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: session.current_url equals `https://other.test/next?q=2#done`

4. Err

5. fail

6. Ok
   - Expected: _display_js(value) equals `/next|?q=2|#done|other.test`

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val assign_result = session.eval_script("location.href = 'https://other.test/next?q=2#done'")
match assign_result:
    Ok(value) =>
        expect(session.current_url).to_equal("https://other.test/next?q=2#done")
    Err(e) =>
        fail("Expected location.href mutation to evaluate: {e}")

val parts_result = session.eval_script("location.pathname + '|' + location.search + '|' + location.hash + '|' + location.host")
match parts_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("/next|?q=2|#done|other.test")
    Err(e) =>
        fail("Expected location parts after href mutation to evaluate: {e}")
```

</details>

#### supports location assign as a history push

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `https://example.com/next?q=1#top`
   - Expected: session.current_url equals `https://example.com/next?q=1#top`
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`

4. Err

5. fail

6. Ok
   - Expected: _display_js(value) equals `/next|?q=1|#top`

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val result = session.eval_script("location.assign('https://example.com/next?q=1#top')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/next?q=1#top")
        expect(session.current_url).to_equal("https://example.com/next?q=1#top")
        expect(session.history.len()).to_equal(2)
        expect(session.current_index).to_equal(1)
    Err(e) =>
        fail("Expected location.assign history push to evaluate: {e}")

val parts_result = session.eval_script("location.pathname + '|' + location.search + '|' + location.hash")
match parts_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("/next|?q=1|#top")
    Err(e) =>
        fail("Expected location parts after assign to evaluate: {e}")
```

</details>

#### supports location replace without appending history

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `https://example.com/replaced`
   - Expected: session.current_url equals `https://example.com/replaced`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`

4. Err

5. fail

6. Some
   - Expected: value.url equals `https://example.com/replaced`

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val result = session.eval_script("location.replace('https://example.com/replaced')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/replaced")
        expect(session.current_url).to_equal("https://example.com/replaced")
        expect(session.history.len()).to_equal(1)
        expect(session.current_index).to_equal(0)
    Err(e) =>
        fail("Expected location.replace to evaluate without appending history: {e}")

val entry = session.current_entry()
match entry:
    Some(value) =>
        expect(value.url).to_equal("https://example.com/replaced")
    nil =>
        fail("Expected current history entry after location.replace")
```

</details>

#### supports history pushState as a location synced history push

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `https://example.com/next?q=1#top`
   - Expected: session.current_url equals `https://example.com/next?q=1#top`
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`

4. Err

5. fail

6. Ok
   - Expected: _display_js(value) equals `/next|?q=1|#top`

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start/index.html", "<html><body>URL</body></html>")

val result = session.eval_script("history.pushState(2, '', 'https://example.com/next?q=1#top')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/next?q=1#top")
        expect(session.current_url).to_equal("https://example.com/next?q=1#top")
        expect(session.history.len()).to_equal(2)
        expect(session.current_index).to_equal(1)
    Err(e) =>
        fail("Expected history.pushState to sync location and append history: {e}")

val parts_result = session.eval_script("location.pathname + '|' + location.search + '|' + location.hash")
match parts_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("/next|?q=1|#top")
    Err(e) =>
        fail("Expected location parts after history.pushState to evaluate: {e}")
```

</details>

#### supports history replaceState without appending history

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `https://example.com/replaced?ok=1`
   - Expected: session.current_url equals `https://example.com/replaced?ok=1`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`

4. Err

5. fail

6. Some
   - Expected: value.url equals `https://example.com/replaced?ok=1`

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val result = session.eval_script("history.replaceState(3, '', 'https://example.com/replaced?ok=1')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/replaced?ok=1")
        expect(session.current_url).to_equal("https://example.com/replaced?ok=1")
        expect(session.history.len()).to_equal(1)
        expect(session.current_index).to_equal(0)
    Err(e) =>
        fail("Expected history.replaceState to sync location without appending history: {e}")

val entry = session.current_entry()
match entry:
    Some(value) =>
        expect(value.url).to_equal("https://example.com/replaced?ok=1")
    nil =>
        fail("Expected current history entry after history.replaceState")
```

</details>

#### supports URLSearchParams in inline browser scripts

1. var session = BrowserSession new

2. "<html><body><script>var params = new URLSearchParams
   - Expected: session.current_body_html equals `function:function:1:true:null:q=2&amp;empty=&amp;tag=a+b&amp;added=hello+worl... (full value in folded executable source)`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/search?q=1&empty=&tag=a+b",
    "<html><body><script>var params = new URLSearchParams(location.search); var before = typeof URLSearchParams + ':' + typeof window.URLSearchParams + ':' + params.get('q') + ':' + params.has('empty') + ':' + params.get('missing'); params.set('q', '2'); params.append('added', 'hello world'); params.append('q', '3'); document.body.textContent = before + ':' + params.toString();</script></body></html>"
)

expect(session.current_body_html).to_equal("function:function:1:true:null:q=2&amp;empty=&amp;tag=a+b&amp;added=hello+world&amp;q=3")
```

</details>

#### exposes secure WebGPU globals

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `object`

4. Err

5. fail

6. Ok
   - Expected: _display_js(value) equals `true:true`

7. Err

8. fail

9. Ok
   - Expected: _display_js(value) equals `true:available`

10. Err

11. fail

12. Ok
   - Expected: _display_js(value) equals `bgra8unorm`

13. Err

14. fail

15. Ok
   - Expected: _display_js(value) equals `function`

16. Err

17. fail

18. Ok
   - Expected: _display_js(value) equals ``

19. Err

20. fail

21. Ok
   - Expected: _display_js(value) equals `Simple WebGPU Software Adapter:available:true`

22. Err

23. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu.html", "<html><body>GPU</body></html>")

val type_result = session.eval_script("typeof navigator.gpu")
match type_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("object")
    Err(e) =>
        fail("Expected secure navigator.gpu type check to evaluate: {e}")

val secure_result = session.eval_script("window.isSecureContext + ':' + navigator.gpu.secureContext")
match secure_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true:true")
    Err(e) =>
        fail("Expected secure WebGPU context flags to evaluate: {e}")

val adapter_result = session.eval_script("navigator.gpu.adapterAvailable + ':' + navigator.gpu.requestAdapterStatus")
match adapter_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true:available")
    Err(e) =>
        fail("Expected WebGPU adapter availability metadata to evaluate: {e}")

val format_result = session.eval_script("navigator.gpu.preferredCanvasFormat")
match format_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("bgra8unorm")
    Err(e) =>
        fail("Expected WebGPU preferred canvas format to evaluate: {e}")

val method_result = session.eval_script("typeof navigator.gpu.requestAdapter")
match method_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function")
    Err(e) =>
        fail("Expected WebGPU requestAdapter method type to evaluate: {e}")

val adapter_request_result = session.eval_script("var adapterName = ''; navigator.gpu.requestAdapter().then(function(adapter) { adapterName = adapter.name + ':' + adapter.requestAdapterStatus + ':' + adapter.isFallbackAdapter; }); adapterName")
match adapter_request_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("")
    Err(e) =>
        fail("Expected WebGPU requestAdapter promise setup to evaluate: {e}")

val adapter_name_result = session.eval_script("adapterName")
match adapter_name_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("Simple WebGPU Software Adapter:available:true")
    Err(e) =>
        fail("Expected WebGPU requestAdapter promise callback result to evaluate: {e}")
```

</details>

#### hides WebGPU globals from insecure pages

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `false`

4. Err

5. fail

6. Ok
   - Expected: _display_js(value) equals `undefined`

7. Err

8. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("http://example.com/webgpu.html", "<html><body>GPU</body></html>")

val secure_result = session.eval_script("window.isSecureContext")
match secure_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("false")
    Err(e) =>
        fail("Expected insecure window.isSecureContext check to evaluate: {e}")

val type_result = session.eval_script("typeof navigator.gpu")
match type_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("undefined")
    Err(e) =>
        fail("Expected insecure navigator.gpu type check to evaluate: {e}")
```

</details>

#### syncs eval script changes back into session state

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `B`
   - Expected: session.current_title equals `B`
   - Expected: session.current_body_html equals `Plain`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:eval", "<html><head><title>A</title></head><body><p>Hi</p></body></html>")

val result = session.eval_script("document.title = 'B'; document.body.textContent = 'Plain'; document.title")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("B")
        expect(session.current_title).to_equal("B")
        expect(session.current_body_html).to_equal("Plain")
    Err(e) =>
        fail("Expected eval script document mutations to sync back to session state: {e}")
```

</details>

#### persists storage objects and cookie jar state

1. var session = BrowserSession new

2. Ok
   - Expected: session.local_storage_item("theme") ?? "" equals `dark`
   - Expected: session.session_storage_item("tab") ?? "" equals `welcome`

3. Err

4. fail

5. Ok

6. Err

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>localStorage.theme = 'dark'; sessionStorage.tab = 'welcome'; document.cookie = 'sid=abc123; Path=/';</script></body></html>"
)
match open_result:
    Ok(_) =>
        expect(session.local_storage_item("theme") ?? "").to_equal("dark")
        expect(session.session_storage_item("tab") ?? "").to_equal("welcome")
        expect(session.document_cookie()).to_contain("sid=abc123")
    Err(e) =>
        fail("Expected storage and cookie writes during page load to persist: {e}")

val reload_result = session.open_html(
    "https://example.com/dashboard",
    "<html><body><script>document.body.textContent = localStorage.theme + ':' + sessionStorage.tab + ':' + document.cookie;</script></body></html>"
)
match reload_result:
    Ok(_) =>
        expect(session.current_body_html).to_contain("dark:welcome:sid=abc123")
    Err(e) =>
        fail("Expected storage and cookie state to persist across page loads: {e}")
```

</details>

#### does not treat cookie attributes as standalone cookies

1. var session = BrowserSession new

2. Ok
   - Expected: session.document_cookie() equals `sid=abc123`
   - Expected: session.cookie_header_for_request("https://example.com/app/next") equals `sid=abc123`
   - Expected: session.cookie_header_for_request("https://example.com/other") equals ``

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>document.cookie = 'sid=abc123; Path=/app';</script></body></html>"
)
match open_result:
    Ok(_) =>
        expect(session.document_cookie()).to_equal("sid=abc123")
        expect(session.cookie_header_for_request("https://example.com/app/next")).to_equal("sid=abc123")
        expect(session.cookie_header_for_request("https://example.com/other")).to_equal("")
    Err(e) =>
        fail("Expected cookie attribute parsing to ignore standalone attributes: {e}")
```

</details>

#### removes cookies when Max-Age=0 is assigned

1. var session = BrowserSession new

2. Ok
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://example.com/app/next") equals ``

3. Err

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>document.cookie = 'sid=abc123; Path=/app'; document.cookie = 'sid=gone; Path=/app; Max-Age=0';</script></body></html>"
)
match open_result:
    Ok(_) =>
        expect(session.document_cookie()).to_equal("")
        expect(session.cookie_header_for_request("https://example.com/app/next")).to_equal("")
    Err(e) =>
        fail("Expected Max-Age=0 document.cookie assignment to remove cookie: {e}")
```

</details>

#### exposes cookie jar update points for future network integration

1. var session = BrowserSession new

2. session open html

3. session apply set cookie header

4. session apply set cookie header
   - Expected: session.cookie_header_for_request("https://example.com/other") equals `global=yes`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Path=/path")
session.apply_set_cookie_header("global=yes; Domain=example.com; Path=/")

expect(session.document_cookie()).to_contain("theme=light")
expect(session.document_cookie()).to_contain("global=yes")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_contain("theme=light")
expect(session.cookie_header_for_request("https://example.com/other")).to_equal("global=yes")
```

</details>

#### removes cookies from Set-Cookie updates when Max-Age=0

1. var session = BrowserSession new

2. session open html

3. session apply set cookie header
   - Expected: session.document_cookie() equals `theme=light`

4. session apply set cookie header
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://example.com/path/next") equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Path=/path")
expect(session.document_cookie()).to_equal("theme=light")

session.apply_set_cookie_header("theme=gone; Path=/path; Max-Age=0")
expect(session.document_cookie()).to_equal("")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_equal("")
```

</details>

#### removes cookies from Set-Cookie updates when Expires is in the past

1. var session = BrowserSession new

2. session open html

3. session apply set cookie header
   - Expected: session.document_cookie() equals `theme=light`

4. session apply set cookie header
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://example.com/path/next") equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Path=/path")
expect(session.document_cookie()).to_equal("theme=light")

session.apply_set_cookie_header("theme=gone; Path=/path; Expires=Thu, 01 Jan 1970 00:00:00 GMT")
expect(session.document_cookie()).to_equal("")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_equal("")
```

</details>

#### matches Set-Cookie domain attributes that include a leading dot

1. var session = BrowserSession new

2. session open html

3. session apply set cookie header
   - Expected: session.document_cookie() equals `theme=light`
   - Expected: session.cookie_header_for_request("https://example.com/path/next") equals `theme=light`
   - Expected: session.cookie_header_for_request("https://sub.example.com/path/next") equals `theme=light`
   - Expected: session.cookie_header_for_request("https://other.com/path/next") equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Domain=.example.com; Path=/")

expect(session.document_cookie()).to_equal("theme=light")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_equal("theme=light")
expect(session.cookie_header_for_request("https://sub.example.com/path/next")).to_equal("theme=light")
expect(session.cookie_header_for_request("https://other.com/path/next")).to_equal("")
```

</details>

#### installs promise globals and settles async fetch after response commit

1. var session = BrowserSession new

2. "<html><body><script>var out = ''; window fetch

3. Ok

4. Ok
   - Expected: _display_js(value) equals `function:function`

5. Err

6. fail

7. Err

8. fail

9. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/data.txt`

10. Ok

11. Ok

12. Err

13. fail

14. Err

15. fail

16. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.txt').then(function(r) { return r.text(); }).then(function(t) { out = t; document.body.textContent = t; });</script></body></html>"
)
match open_result:
    Ok(_) =>
        val promise_result = session.eval_script("typeof Promise.resolve + ':' + typeof Promise.prototype.then")
        match promise_result:
            Ok(value) =>
                expect(_display_js(value)).to_equal("function:function")
            Err(e) =>
                fail("Expected Promise globals to evaluate after fetch setup: {e}")
    Err(e) =>
        fail("Expected async fetch setup page to load: {e}")

match session.take_pending_request():
    Some(request) =>
        expect(request.kind).to_equal("fetch")
        expect(request.url).to_equal("https://example.com/data.txt")
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Set-Cookie: token=abc; Path=/\n",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val out_result = session.eval_script("out + ':' + document.body.textContent + ':' + document.cookie")
                match out_result:
                    Ok(value) =>
                        expect(_display_js(value)).to_contain("alpha:alpha")
                        expect(_display_js(value)).to_contain("token=abc")
                    Err(e) =>
                        fail("Expected settled fetch output and cookie to evaluate: {e}")
            Err(e) =>
                fail("Expected network response commit for fetch to succeed: {e}")
    nil:
        fail("Expected pending fetch request after page load")
```

</details>

#### supports fetch then chaining through the browser promise path

1. var session = BrowserSession new

2. "<html><body><script>var out = ''; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `alpha`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.txt').then(function(r) { return r.text(); }).then(function(t) { out = t; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("alpha")
                    Err(e) =>
                        fail("Expected fetch then-chain output to evaluate: {e}")
            Err(e) =>
                fail("Expected fetch then-chain network response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for then-chain")
```

</details>

#### supports fetch response blob metadata and text

1. var session = BrowserSession new

2. "<html><body><script>var out = ''; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `5:text/plain:alpha`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.bin').then(function(r) { return r.blob(); }).then(function(b) { out = b.size + ':' + b.type; return b.text(); }).then(function(t) { out = out + ':' + t; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: text/plain\n",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("5:text/plain:alpha")
                    Err(e) =>
                        fail("Expected fetch response blob metadata/text output to evaluate: {e}")
            Err(e) =>
                fail("Expected fetch blob response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for blob response")
```

</details>

#### supports fetch promise rejection on transport error

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; window fetch

3. Some

4. Err
   - Expected: e equals `network down`

5. Ok
   - Expected: _display_js(value) equals `network down`

6. Err

7. fail

8. Ok

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; window.fetch('/data.txt').catch(function(err) { out = err; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 0,
            headers: "",
            body: "",
            error: "network down"
        ))
        match commit_result:
            Err(e) =>
                expect(e).to_equal("network down")
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("network down")
                    Err(err) =>
                        fail("Expected fetch rejection handler output to evaluate: {err}")
            Ok(_) =>
                fail("Expected transport-error response commit to reject")
    nil:
        fail("Expected pending fetch request for transport-error path")
```

</details>

#### follows location changes through session owned navigation

1. var session = BrowserSession new

2. session register resource

3. Ok
   - Expected: session.current_url equals `https://example.com/next`
   - Expected: session.current_title equals `Next`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/next", "<html><head><title>Next</title></head><body>After</body></html>")
val result = session.open_html(
    "https://example.com/start",
    "<html><body><script>location.href = 'https://example.com/next';</script>Start</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("https://example.com/next")
        expect(session.current_title).to_equal("Next")
        expect(session.current_body_html).to_contain("After")
    Err(e) =>
        fail("Expected script-owned location change to navigate through session resource: {e}")
```

</details>

#### implements storage method surface while keeping property access compatible

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:function:function:function:function`

4. Err

5. fail

6. "sessionStorage setItem

7. Ok
   - Expected: _display_js(value) equals `7:2:tab:mode`
   - Expected: session.session_storage_item("tab") ?? "" equals `7`
   - Expected: session.session_storage_item("mode") ?? "" equals `reader`

8. Err

9. fail

10. "sessionStorage removeItem

11. Ok
   - Expected: _display_js(value) equals `true:1:mode`

12. Err

13. fail

14. "localStorage theme = 'dark'; localStorage getItem

15. Ok
   - Expected: _display_js(value) equals `dark:0`

16. Err

17. fail

18. Ok
   - Expected: _display_js(value) equals `1:theme`
   - Expected: session.local_storage_item("theme") ?? "" equals `dark`

19. Err

20. fail

21. "localStorage clear

22. Ok
   - Expected: _display_js(value) equals `0:0:true`

23. Err

24. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:storage", "<html><body>Storage</body></html>")

val method_result = session.eval_script(
    "typeof sessionStorage.getItem + ':' + typeof sessionStorage.setItem + ':' + typeof sessionStorage.removeItem + ':' + typeof sessionStorage.clear + ':' + typeof sessionStorage.key"
)
match method_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:function:function:function:function")
    Err(e) =>
        fail("Expected storage method surface type check to evaluate: {e}")

val set_result = session.eval_script(
    "sessionStorage.setItem('tab', 7); sessionStorage.setItem('mode', 'reader'); sessionStorage.getItem('tab') + ':' + sessionStorage.length + ':' + sessionStorage.key(0) + ':' + sessionStorage.key(1)"
)
match set_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("7:2:tab:mode")
        expect(session.session_storage_item("tab") ?? "").to_equal("7")
        expect(session.session_storage_item("mode") ?? "").to_equal("reader")
    Err(e) =>
        fail("Expected sessionStorage setItem/getItem/key flow to evaluate: {e}")

val remove_result = session.eval_script(
    "sessionStorage.removeItem('tab'); (sessionStorage.getItem('tab') === null) + ':' + sessionStorage.length + ':' + sessionStorage.key(0)"
)
match remove_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true:1:mode")
        expect(session.session_storage_item("tab")).to_be_nil()
    Err(e) =>
        fail("Expected sessionStorage removeItem flow to evaluate: {e}")

val property_result = session.eval_script(
    "localStorage.theme = 'dark'; localStorage.getItem('theme') + ':' + localStorage.length"
)
match property_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("dark:0")
    Err(e) =>
        fail("Expected localStorage property assignment compatibility flow to evaluate: {e}")

val synced_length_result = session.eval_script("localStorage.length + ':' + localStorage.key(0)")
match synced_length_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("1:theme")
        expect(session.local_storage_item("theme") ?? "").to_equal("dark")
    Err(e) =>
        fail("Expected localStorage synced length/key flow to evaluate: {e}")

val clear_result = session.eval_script(
    "localStorage.clear(); sessionStorage.clear(); localStorage.length + ':' + sessionStorage.length + ':' + (localStorage.getItem('theme') === null)"
)
match clear_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("0:0:true")
        expect(session.local_storage_item("theme")).to_be_nil()
        expect(session.session_storage_item("mode")).to_be_nil()
    Err(e) =>
        fail("Expected storage clear flow to evaluate: {e}")
```

</details>

### BrowserSession history and rendering

#### supports back forward and reload

1. var session = BrowserSession new

2. session open html

3. session open html
   - Expected: session.can_go_back() is true
   - Expected: session.can_go_forward() is false

4. Ok
   - Expected: session.current_url equals `about:one`
   - Expected: session.current_title equals `One`

5. Err

6. fail

7. Ok
   - Expected: session.current_url equals `about:two`
   - Expected: session.current_title equals `Two`

8. Err

9. fail

10. Ok
   - Expected: session.current_url equals `about:two`

11. Err

12. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:one", "<html><head><title>One</title></head><body>One</body></html>")
session.open_html("about:two", "<html><head><title>Two</title></head><body>Two</body></html>")

expect(session.can_go_back()).to_equal(true)
expect(session.can_go_forward()).to_equal(false)

val back_result = session.go_back()
match back_result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:one")
        expect(session.current_title).to_equal("One")
    Err(e) =>
        fail("Expected browser session go_back to succeed: {e}")

val forward_result = session.go_forward()
match forward_result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:two")
        expect(session.current_title).to_equal("Two")
    Err(e) =>
        fail("Expected browser session go_forward to succeed: {e}")

val reload_result = session.reload()
match reload_result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:two")
        expect(session.current_body_html).to_contain("Two")
    Err(e) =>
        fail("Expected browser session reload to succeed: {e}")
```

</details>

#### renders current body through browser renderer

1. var session = BrowserSession new
   - Expected: render.width equals `320`
   - Expected: render.height equals `200`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:render",
    "<html><body><div style='background-color: #ff0000'><span>Hello</span></div></body></html>"
)
val render = session.render(320, 200)
expect(render.width).to_equal(320)
expect(render.height).to_equal(200)
expect(render.node_count).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession lifecycle
- BrowserSession page loading
- BrowserSession script bridge
- BrowserSession history and rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
