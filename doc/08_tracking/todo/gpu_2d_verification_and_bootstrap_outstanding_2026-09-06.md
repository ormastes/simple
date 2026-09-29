# GPU/2D lane — outstanding verification and bootstrap work

**Opened:** 2026-09-06. One entry per outstanding item. Every implementation
item in this lane is complete in source; what remains is evidence, plus two
things that are blocked on hardware or a build this session is forbidden to run.

Source-anchored entries also carry a `TODO(P2,...)` comment at the code site so
`bin/simple todo-scan` picks them into `doc/08_tracking/todo/todo_db.sdn`. The
scan was NOT run here: `bin/simple` on this host is the bootstrap CLI and has no
`todo-scan` subcommand, and rebuilding one is a bootstrap, which is frozen. The
comments are in place, so the next scan on a host with a full CLI collects them
without further work.

| # | Item | State | Evidence that closes it |
|---|---|---|---|
| 1 | Metal packed font path executes on a device | VERIFICATION PENDING, blocked on build | One real frame on a Metal-featured binary: device pixels equal the CPU mirror for the same batch, and the frame contract observes 1 command / 1 commit / 1 wait |
| 2 | Metal/Vulkan parity is pixel-level, not just layout-level | VERIFICATION PENDING, blocked on build | Both backends composite the same batch on real devices and produce identical pixels |
| 3 | Metal host staging pool holds across a real frame | VERIFICATION PENDING, blocked on build | A device run showing the staging pointer unchanged across two frames of differing batch size |
| 4 | Engine reuse cache invalidates correctly on a real device | VERIFICATION PENDING, blocked on build | A device run where a `completion_unknown` engine is discarded and a fresh one created, observed rather than simulated |
| 5 | Engine cache drain wired to a teardown | NOT STARTED, no seam exists | A surface or session teardown seam that calls both drains, plus a spec asserting both pools are empty afterwards |
| 6 | Web route key stops hashing the whole scene per frame | NOT STARTED, prerequisite landed but insufficient | The rebuild path reuses a retained composition, proven by a spec counting serializations across two frames of unchanged HTML |
| 7 | Presenter twin pixels-equal comparison | NOT STARTED | The same treatment the fast path's fingerprint received, with a spec proving a genuine mismatch is still caught |
| 8 | DirectX 2D GPU text path | NOT STARTED, blocked on hardware | An HLSL twin of the packed composite, a frame-record opcode, the `rt_directx_*` entries, and one real frame on Windows or DXVK |
| 9 | Six showcase fixture painters | NOT STARTED, deliberate | The six painters implemented; until then six spec scenarios stay honestly red rather than being rewritten to match a solid fill |
| 10 | Chrome comparison Simple side | NOT STARTED | The renderer linked into `simple_runner.spl` so it emits `source="measured"`; the fail-closed guard already prevents a synthetic side being reported as measured |
| 11 | `todo-scan` regenerates `todo_db.sdn` with these entries | BLOCKED ON BOOTSTRAP | A host with a full-CLI `simple` runs `todo-scan`; the source `TODO(P2,...)` comments are already in place for it |

## What is NOT outstanding

Every implementation item in this lane is real code, checked at the source
rather than assumed: the Metal packed dispatch calls the real SFFI dispatch,
commit and wait; the scheduler's strict fallback reads `fallback_explicit`; the
engine cache calls `shutdown()` on anything it will not park. None of them is a
stub, a canned value, or a fake path.

The only thing no item in this lane has is DEVICE evidence, because this host
has no Metal-featured binary and producing one is a bootstrap. That is a single
shared blocker, listed once per affected item above rather than hidden.
