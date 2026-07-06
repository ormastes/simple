# Claude Full Session Storage Project

> Checks Project parity for encoded project paths, transcript append chains, message removal, flush state, and test reset hooks.

<!-- sdn-diagram:id=sessionStorage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sessionStorage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sessionStorage_spec -> std
sessionStorage_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sessionStorage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Session Storage Project

Checks Project parity for encoded project paths, transcript append chains, message removal, flush state, and test reset hooks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/sessionStorage_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `manual companion matching simple spipe-docgen layout` |

## Scenarios

### Claude full utils sessionStorage Project

#### tracks a project transcript chain and flush snapshot

- Create a project in an encoded cwd and append two message entries.
- Verify encoded project directory, transcript path, message count, parent UUID, last UUID, and session id lookup.
- Remove a message, flush the JSONL-style snapshot, and reset flush state.
- Verify removal, flush completion, flush count, serialized write content, reset count, and source line parity marker.

</details>
