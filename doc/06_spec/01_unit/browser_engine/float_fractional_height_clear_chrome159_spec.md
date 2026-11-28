# Float Fractional Height Clear (Chrome 159)

> Traceability: `REQ-WEB-FLOAT-BOTTOM-FRACTION-001` & `REQ-WEB-001` — sub-pixel float bottom propagation and CSS 2.2 Appendix E right-float overlap above `clear:left`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

## Scenarios

- **AC-1..AC-7, AC-9..AC-10**: Exact fractional float bottoms across `clear`, `max-height`, margins, `flow-root`, and stacked floats (`k=1` and `k=4`).
- **AC-8**: `clear:left` clears the 10.25px left float only while the 10.75px right float (`0x332211u32`) paints on top of the overlapping `clear:left` block (`1600..1642` at `k=4`, `400..410` at `k=1`).
