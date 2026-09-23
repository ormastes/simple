# Windows Phase 2 exact92 link blockers (2026-09-23)

Status: OPEN. Final capped Phase 2 run failed; no compiler/interpreter/loader tests ran.

Source `92af30bcf3dc7c1a79724479a513c2373d04628e` produced an admitted Stage 2 compiler (`14b95f58807b92ee75ed72028630dfc888e5dfd38b373612098851e3cd83d716`; 902 compiled, zero failed). Canonical Phase 2 used 12 build threads and 12 test workers, isolated `D:/p2w92` and `D:/p2c92`. Its summary is `D:/p2w92/summary.env`; the retained handoff is `build/mini_builds/phase2-92/FAILURE-HANDOFF.md`.

- Full CLI: Windows archive batching advanced past the prior error 206, but `lld-link` rejected duplicate `spl_str_ptr` (only `simple_runtime.lib(runtime_native.obj)` is printed as an owner) and `rt_webgpu_create_surface`, `rt_webgpu_init`, `rt_webgpu_destroy_surface` (both `runtime_native.obj` and the hosted-runtime Rust rlib define each WebGPU symbol). See `D:/p2w92/logs/compiler_cli_build.log:1334`.
- Test runner: link stopped at unresolved `rt_cli_run_tests_process_args`, followed by shell, TCP, daemon, and CUDA provider exports; the linker error limit means this inventory is incomplete. See `D:/p2w92/logs/test_runner_build.log:1221`.
- MCP and LSP builds and help commands passed. The 11 dependent check/test tasks were `UNSUPPORTED` because the full CLI artifact was absent; there are no `Results:` records or test-pass counts.

Do not infer a missing second owner for `spl_str_ptr` or add blanket C stubs for unresolved providers. Restore explicit symbol ownership and a bounded provider closure, then admit a new exact-source Stage 2 before replaying Phase 2. This session reached the three-cycle verification cap; no fourth run was started.
