# Simple 2D showcase hardening test plan

| Requirement | Required evidence |
| --- | --- |
| REQ-003 | nonblank primitive gallery/readback |
| REQ-008 | compositor output retains desktop < child < taskbar order |
| REQ-009 | key, pointer-move, and click pass through `WindowEventLoop` |
| REQ-010 | selected font, cold rasterization, warm-cache reuse |
| REQ-011 | >=60 changed redraws and p95 <=33.33 ms |
| REQ-012 | guide, expert wiki, and SPipe contract link together |

The source-contract test prevents removal of the required owners. Live
acceptance remains fail-closed: blank/static frames, synthetic handles, or raw
Winit-only event counts cannot satisfy it. Do not begin web, GUI, or WM user
verification until the user has accepted the live 2D showcase.
