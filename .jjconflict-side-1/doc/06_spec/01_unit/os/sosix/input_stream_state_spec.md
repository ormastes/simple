# SOSIX Input Stream State Specification

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 6 | 6 | 0 | 0 |

The executable source is
`test/01_unit/os/sosix/input_stream_state_spec.spl`. It proves ordered
publication/consumption, monotonic timestamps, bounded backpressure,
motion-only coalescing, and drain-after-close behavior. Key/button/text events
are never silently coalesced.

