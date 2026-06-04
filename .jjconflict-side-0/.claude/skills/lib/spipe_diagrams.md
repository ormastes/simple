# SPipe Diagram & Concision Rules

## 30-Line Rule

Phase doc prose must be **≤30 lines** of readable content. Tables and diagrams are excluded from the count. Focus on "what changed and why" — not exhaustive enumeration.

## Diagram Requirement

Every phase doc output must include **≥1 SDN diagram**. Diagram type varies by phase:

| Phase | Diagram Kind | Purpose |
|-------|-------------|---------|
| Research | Context/dependency map | What exists, what relates |
| Architecture | Component/flow diagram | Modules, interfaces, data flow |
| Design | Sequence/interaction diagram | Who calls whom, in what order |
| Refactor | Before/after structural comparison | What changed structurally |

## SDN Diagram Format

Use the `<!-- sdn-diagram:id=... -->` Markdown format with two `<details>` blocks:

```markdown
<!-- sdn-diagram:id=<feature>.<phase> -->
<details class="sdn-source">
<summary>SDN source</summary>

` ` `sdn id=<feature>.<phase> hash=sha256:auto render=ascii
@layout dag
@direction LR

ModuleA -> ModuleB
ModuleB -> ModuleC
` ` `

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

` ` `ascii generated-from=<feature>.<phase> hash=sha256:auto
# run: simple md-diagram-update
` ` `

</details>
<!-- sdn-diagram:end -->
```

Use `hash=sha256:auto` as placeholder. Run `simple md-diagram-update` to fill in real hash + ASCII art.

## SDN Graph Syntax Quick Reference

- **Nodes:** Just name them in edges, or declare explicitly: `NodeName`
- **Edges:** `A -> B` (normal), `A ~> B` (async), `A -x B` (forbidden)
- **Direction:** `@direction LR` (left-to-right) or `@direction TB` (top-to-bottom)
- **Layout:** `@layout dag` (directed acyclic graph)

## Example: Architecture Phase Doc (≤30 lines + 1 diagram)

```markdown
# Auth Module Architecture

The auth subsystem splits into three modules: login handles credential validation,
token manages JWT lifecycle, and middleware intercepts requests for token checks.

<!-- sdn-diagram:id=auth.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

` ` `sdn id=auth.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

login -> token
middleware -> token
` ` `

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

` ` `ascii generated-from=auth.arch hash=sha256:auto
+-------+      +-------+
| login | ---> | token |
+-------+      +-------+
+------------+     |
| middleware | ----+
+------------+
` ` `

</details>
<!-- sdn-diagram:end -->

| Module | Responsibility |
|--------|---------------|
| login.spl | Credential validation, session creation |
| token.spl | JWT generation, verification, expiry |
| middleware.spl | Request interception, token enforcement |

login depends on token for JWT creation. middleware depends on token for verification.
No circular dependencies. token is the shared core.
```
