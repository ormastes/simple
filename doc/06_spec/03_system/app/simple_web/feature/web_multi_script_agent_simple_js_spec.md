# Multi-Script Web Engine (`JS Engine`, `Simple Script`, `Agent Script`) Specification

> Verifies hardened JavaScript execution, declarative `AgentScriptExecutor` automation verbs & SDN receipts, and cooperative document-order `<script>` + `<script type="text/simple">` + `<script type="text/agent">` HTML rendering through `web_multi_script_run_and_render_html`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Category | Application |
| Status | Active |
| Requirements | REQ-WEB-009 |
| Plan | `doc/03_plan/sys_test/simple_web_engine_completion.md` |
| Source | `test/03_system/app/simple_web/feature/web_multi_script_agent_simple_js_spec.spl` |
| Updated | 2026-11-28 |

## Scenarios

1. **Hardened JS Engine expressions & builtins:** Verifies floating-point literals, `Math.max`/`min`/`round`/`floor`/`ceil`, `parseInt`/`parseFloat` with CSS unit suffixes (`42px`, `3.5rem`) and hex (`0xff`), `JSON.parse`/`JSON.stringify`, template literals, closures, `+=` compound assignments, array `filter`/`map`/`forEach`/`join`, and string `trim`/`replace`/`split`/`includes`.
2. **Agent Script (`text/agent` / `application/agent-script`) automation & SDN receipt:** Executes `fill`, `select`, `check`, `uncheck`, `hover`, `click`, `submit`, `set_text`, `set_attr`, `set_style`, `add_class`, `remove_class`, `drag`, `expect_text`, `expect_attr`, and `log`, verifying DOM mutations, failed-expectation handling, and canonical SDN receipt formatting.
3. **Cooperative multi-script pipeline render (`520x340`):** Executes `<script>` (JS creates `.row` items), `<script type="text/simple">` (computes `sum_attr`/`count` summary & border style), and `<script type="text/agent">` (checks checkbox, updates approval badge, asserts summary) in document order on one shared `BeDomNode` tree and rasterizes a valid multi-color `520x340` framebuffer.
