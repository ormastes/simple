# SOSIX Display Surface State Specification

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 6 | 6 | 0 | 0 |

The executable source is
`test/01_unit/os/sosix/display_surface_state_spec.spl`. It proves bounded
frame submission, ordered completion, duplicate/stale rejection, resize
generation invalidation, and drained close behavior. The state is backend-free;
hosted and SimpleOS display adapters consume it without moving Draw IR or GPU
resources into SOSIX.

