# Stage4 standalone AOT rejects a newly opened backend session lease

- **Status:** Open
- **Found:** 2026-09-29, Linux ARM64 exact Stage4 compiler hello AOT
- **Impact:** blocks a current-source hello executable and its size/startup/RSS gates

The exact Stage4 compiler links and passes `--version`. Ordinary positional
AOT did not install the selected K1 table; the entry now installs it before
JIT/AOT work, and the hello request advances past `PLUG-E-NOTFOUND`.
Positional AOT then reached native compilation with an empty MIR stub. The
driver now lowers positional `cli_mode_text == "aot"` sources, and the same
hello request advances into the backend session.

The backend first reports `backend session lease is retired` from
`BackendSessionOwnedLeaseV2.compile_aot_into_path`. A diagnostic trial removed
that copied scalar guard, but `backend_session_authority_use_acquire_v2`
then rejected the token (`backend session use rejected: 0`). The trial was
reverted: the authority also refuses the lease, so bypassing the guard is not
a fix. The exact cause of the lease state is not established.

**Next:** trace owner identity, token generation, record state, and lease
copies at `open`, `_compile_to_native_with_backend_session`,
`_compile_selected_module`, and `use_acquire`; repair the lifetime transfer
without weakening authority checks. Then require hello AOT to produce and run
a real executable before the matched size/startup/RSS cohort. This session
stopped after three focused build/check cycles.

Evidence: `build/mini_builds/target5_stage4_k1_install.log`,
`target5_stage4_k1_hello.log`, `target5_stage4_k1_mir_build.log`,
`target5_stage4_k1_mir_hello.log`, `target5_stage4_k1_lease_build.log`, and
`target5_stage4_k1_lease_hello.log` under `build/mini_builds/`.
