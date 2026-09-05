# Web layout manager system test plan

| Requirement | Evidence |
|---|---|
| REQ-WLM-001 | Real root+child renderer result proves `raw_boxes`, `i + 1`, DOM-route, parent, and bx/by/bw/bh conversion |
| REQ-WLM-002 | All eight fingerprint classifications plus total profile admission |
| REQ-WLM-003 | insert, font resource, and viewport fixtures produce stable frontiers |
| REQ-WLM-004 | full and incremental calls return framework receipts |
| REQ-WLM-005 | epochs increase once; `LayoutOf` and hit regions remain generation-qualified |
| REQ-WLM-006 | stale generation and unsupported profile fixtures fault before execution |

Frozen manual steps: “Capture the CPU layout oracle”, “Classify browser layout islands”, “Apply the invalidated frontier”, and “Verify fragments mappings and hit index”.

Required edge fixtures: none, contents, table-cell, unknown display, hidden-vs-auto overflow, absolute image, mixed fonts, and preserved nowrap whitespace.
