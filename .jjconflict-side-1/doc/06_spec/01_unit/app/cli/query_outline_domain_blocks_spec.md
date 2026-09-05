# Query Outline Domain Blocks Specification

> <details>

<!-- sdn-diagram:id=query_outline_domain_blocks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_outline_domain_blocks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_outline_domain_blocks_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_outline_domain_blocks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Outline Domain Blocks Specification

## Scenarios

### query outline domain blocks

#### exposes top-level domain blocks in the outline surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "p=/tmp/simple_query_outline_domain_probe.spl; printf 'use app.cli.query_outline.{OutlineOptions, parse_outline_source}\\nfn main():\\n    val source = \"schemaBlock\\\\nstyleBlock\\\\nval schema = 1\\\\n\"\\n    val outline = parse_outline_source(source, OutlineOptions(parent_for_types: true, include_import_symbols: false, include_fields: true, extract_binding_types: false))\\n    print(outline[0].name)\\n    print(outline[0].token_start)\\n    print(outline[0].token_end)\\n    print(outline[1].name)\\n    print(outline[1].token_start)\\n    print(outline[1].token_end)\\n    print(outline[2].name)\\n    print(outline[2].token_start)\\n    print(outline[2].token_end)\\n' > $p; SIMPLE_LIB=src bin/simple run $p"
val (out, _err, code) = rt_process_run("/bin/sh", ["-c", script])

expect(code).to_equal(0)
expect(out).to_contain("schema" + "{}")
expect(out).to_contain("0\n6")
expect(out).to_contain("style" + "{}")
expect(out).to_contain("0\n5")
expect(out).to_contain("schema")
expect(out).to_contain("4\n10")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_outline_domain_blocks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query outline domain blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
