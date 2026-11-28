# `auto` Tracks in `grid-template-columns` (Chrome 159)

> Traceability: `REQ-WEB-002` — CSS Grid `auto` track `max-content` measurement resolves percentage margins against `0` for wrapped and direct `display:flex` grid items.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

## Scenarios

- **AC-1..AC-5**: Wrapped flex `auto` tracks, `fr` remainders, multi-`auto` sharing, `column-gap`, and text max-content (`k=1` and `k=4`).
- **AC-6**: A direct `display:flex` grid item in `grid-template-columns: auto 1fr` with a `margin-left:10%; width:40px` child resolves `%` margin against `0` during intrinsic track sizing (`44..79` at `k=1`, `176..319` at `k=4`).
