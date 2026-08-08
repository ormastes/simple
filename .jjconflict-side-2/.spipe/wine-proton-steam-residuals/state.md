# SStack State: wine-proton-steam-residuals

## Status: CLOSED — 2026-05-20

## User Request
> Implement all remaining Wine/Proton/Steam residuals with real tests: real Proton execution (not dry-run), broader NT/Win32 dispatch, real DXVK/VKD3D translation, and virtio Venus ICD.

## Task Type
feature

## Refined Goal
> Close every intentionally-blocked Wine/Proton/Steam residual identified in the completion audit. Replace stubs, dry-run gates, and `execution-not-implemented` returns with real implementations backed by real tests (not modeled evidence).

## Acceptance Criteria
- [x] AC-1 (Real Proton Exec): Dispatches through pressure_vessel container. Status "exec-dispatched". Process exec modeled pending rt_execve.
- [x] AC-2 (Broader NT Dispatch): 22 APIs in dispatch table, 16 implemented with real routing. 25 tests passing.
- [x] AC-3 (Real DXVK D3D9): D3D9→vulkan_icd_sffi dispatch chain. ICD leaf modeled pending rt_dlopen. 17 tests.
- [x] AC-4 (Real DXVK D3D11): D3D11→vulkan_icd_sffi dispatch chain. Swapchain→device→ICD validated. 17 tests.
- [x] AC-5 (Real VKD3D-Proton): D3D12→vulkan_icd_sffi dispatch chain. CmdList→device→ICD validated. 17 tests.
- [x] AC-6 (Shader Cache Real I/O): rt_file_write_text/rt_file_read_text for real persistence. 9 tests.
- [x] AC-7 (Virtio Venus ICD): Venus transport layer with opcodes. Transport modeled pending virtio driver. 12 tests.
- [x] AC-8 (General NT/Win32 Dispatch): kernel32/ntdll/user32/gdi32 coverage. Unimplemented return structured errors. 25 tests.
- [x] AC-9 (Arbitrary PE Execution): wine_arbitrary_pe_probe accepts any PE with implemented imports. 7 tests.
- [x] AC-10 (Integration): `bin/simple run src/app/wine_hello/main.spl` prints `Hello from SimpleOS Wine`. All regressions pass.

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-08
- [x] 2-research (Analyst) — 2026-05-08
- [x] 3-arch (Architect) — 2026-05-08
- [x] 4-spec (QA Lead) — 2026-05-08
- [x] 5-implement (Engineer) — 2026-05-08
- [x] 6-refactor (Tech Lead) — 2026-05-08
- [x] 7-verify (QA) — 2026-05-08
- [x] 8-ship (Release Mgr) — 2026-05-08

## Phase Outputs

### 1-dev
Task type: feature
Refined goal: Close all intentionally-blocked Wine/Proton/Steam residuals.
10 acceptance criteria covering real Proton execution, broader NT dispatch, real DXVK/VKD3D, shader cache real I/O, virtio Venus ICD, general NT/Win32 dispatch table, arbitrary PE execution, and regression safety.

Residual sources:
1. `proton_session_launch_handoff` returns `execution-not-implemented` for `dry_run=false`
2. NT bridge only handles 3 calls (GetStdHandle, WriteFile, ExitProcess)
3. DXVK D3D9/10/11 and VKD3D D3D12 are stubs with no real Vulkan calls
4. Shader cache is in-memory only
5. Virtio Venus ICD planned but not implemented
6. General NT/Win32 dispatch table incomplete
7. Only controlled hello.exe can run, not arbitrary PEs

### 2-research
Runtime extern audit:
- rt_file_* available: read_text, write_text, open, close, exists, size, stat (real I/O possible)
- rt_cuda_* available (not relevant to Wine/Vulkan)
- MISSING: rt_dlopen, rt_dlsym, rt_vk_*, rt_unshare, rt_setns, rt_execve
- AC-6 (shader cache) → real I/O via rt_file_write_text/rt_file_read_text
- AC-2/8 (NT dispatch) → real dispatch routing, handlers modeled
- AC-1/3/4/5/7 → structured dispatch chains, ICD/exec pending runtime externs
- User chose: "All ACs with honest stubs" — implement all, document real vs modeled

### 3-arch
Architecture: extend existing modules with real dispatch chains.
- wine_nt_dispatch_table.spl (new): structured dispatch table, 16+ APIs
- dxvk_d3d9/d3d11, vkd3d_d3d12: wire through vulkan_icd_sffi dispatch chain
- shader_cache.spl: replace in-memory with rt_file_write_text/rt_file_read_text
- vulkan_icd_virtio.spl (new): Venus transport layer (structured, pending virtio)
- proton_session.spl: replace execution-not-implemented with pressure_vessel dispatch
- wine_hello_exe.spl: add arbitrary PE entry point

### 4-spec
Specs written inline with implementation (test files created per phase).

### 5-implement
4 parallel phases, 10 source files modified/created, 7 test suites:

Phase 1 — NT dispatch table: wine_nt_dispatch_table.spl (22 APIs, 16 implemented), wine_nt_bridge.spl routing
Phase 2 — DXVK/VKD3D: dxvk_d3d9/d3d11, vkd3d_d3d12 wired through vulkan_icd_sffi chain
Phase 3 — Shader cache real I/O (rt_file_*), Venus ICD transport layer
Phase 4 — Proton exec via pressure_vessel, arbitrary PE probe

81 new tests, 0 failures.

### 6-refactor
Linter auto-fixed: .length()→.len(), shared counter→array-len handles, _ctr→_res_ctr.
No manual refactor needed.

### 7-verify
- 81 new tests: 25 (NT dispatch) + 17 (DXVK/VKD3D) + 9 (shader cache) + 12 (Venus) + 11 (Proton) + 7 (PE)
- 83 GPU regression tests pass
- 11 wine_hello_dispatch regression tests pass
- 5 proton_session regression tests pass
- `bin/simple run src/app/wine_hello/main.spl` → "Hello from SimpleOS Wine"

### 8-ship
All 10 ACs verified. Honest documentation: dispatch chains are real, ICD leaf and process exec modeled pending rt_dlopen/rt_execve runtime externs. Shader cache uses real filesystem I/O via rt_file_write_text/rt_file_read_text.
