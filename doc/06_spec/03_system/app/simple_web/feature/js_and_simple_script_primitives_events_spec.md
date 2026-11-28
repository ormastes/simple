# Web Engine: JS Engine & Simple Script Primitives + Events Parity

> Verifies JavaScript (`<script>`) and Simple Script (`<script type="text/simple">`) primitive features, DOM mutations, interactive event handling (`click`, `<select>` `change`, container `wheel` scroll, floating window `mousedown`/`mousemove`/`mouseup` drag), clean GC-safe console logging, and pixel render parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_web/feature/js_and_simple_script_primitives_events_spec.spl` |
| Requirement | `REQ-WEB-JS-SS-PRIM-EVENTS-001` |
| Updated | 2026-11-28 |

## Scenarios

### JS Engine & Simple Script Primitives + Events Parity

#### verifies JS and Simple Script primitive numbers, strings, booleans, arrays, objects, and closures

- Evaluate the primitives matrix in `JsRuntime` (`2.6 * 4`, `1e-3`, `2.5e-2`, `%`, `+=`/`-=`/`*=`, `++`/`--`, `Math.round`/`floor`/`ceil`/`clamp`, `parseFloat`, string `trim`/`slice`/`substring`/`indexOf`/`split`, template literals, strict booleans, array `push`/mutation/loops, object mutations, and closures).
  - Expected: Exact output `"10.4 ; 0.001 ; 0.025 ; 2 ; 39 ; 2 ; 3,2,3,100 ; 0.025 ; hello ; world ; 6 ; hello|world|js ; v=10.4|pf=0.025 ; true ; true ; 3 ; 75 ; 30 ; 21"`.
- Evaluate the matching matrix in `SimpleScriptDomVm` (`fn(w): w * 5` inline lambda, closure `make_mul`, mutable map `{label: "box", n: 7}`, `===`/`!==`/`&&`/`||` and `and`/`or`/`not`, `{expr}` interpolation).
  - Expected: `execute` returns `true` with empty error and matching `vm.logs[0]`.

#### renders JS and Simple Script primitive pages to identical DOM state and pixels via web_multi_script_run_and_render_html

- Run `web_multi_script_run_and_render_html` at `160x120` on both the `<script>` and `<script type="text/simple">` primitive specimen pages.
  - Expected: Identical DOM outputs (`#status-badge == "PASS"`, `#num-out`, `#str-out`, `#bool-out`, `#arr-out`, `#obj-out`) and `0` differing pixels between JS and Simple Script framebuffers.

#### dispatches click, select change, wheel scroll, and floating window drag in BrowserSession with pixel updates

- Open the dual `<script>` + `<script type="text/simple">` interactive page in `BrowserSession` and capture the `160x120` baseline pixel buffer.
- Dispatch `click` (x2), `<select>` `change` (`"beta"`), container `wheel` (`deltaY = 48.0` with `preventDefault()`), and floating window drag (`mousedown` -> `mousemove` -> `mouseup` on `#js-float-bar` and `#ss-float-bar`).
  - Expected: Both JS and Simple Script counters equal `"2"`, dropdown outputs equal `"beta"`, badges display `"beta:2"` with `#16a34a`, scroll readouts equal `"48"`, floating window styles update (`left:30px;top:138px;` and `left:150px;top:138px;`), `element_scroll_ids` tracks both scroll containers, `console_logs()` contains exact clean entries without stale object aliasing, and the post-event `160x120` render differs from baseline by `> 200` pixels.

</details>
