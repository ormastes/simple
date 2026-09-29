# Stage4 standalone AOT rejects a newly opened backend session lease

- **Status:** Fixed for the tested Stage4 hello path; broader tests pending
- **Found:** 2026-09-29, Linux ARM64 exact Stage4 compiler hello AOT
- **Impact:** blocks a current-source hello executable and its size/startup/RSS gates

The exact Stage4 compiler links and passes `--version`. Ordinary positional
AOT did not install the selected K1 table; the entry now installs it before
JIT/AOT work, and the hello request advances past `PLUG-E-NOTFOUND`.
Positional AOT then reached native compilation with an empty MIR stub. The
driver now lowers positional `cli_mode_text == "aot"` sources, and the same
hello request advances into the backend session.

The backend initially reported `backend session lease is retired` from
`BackendSessionOwnedLeaseV2.compile_aot_into_path`. A diagnostic trial removed
that copied scalar guard, but `backend_session_authority_use_acquire_v2`
then rejected the token (`backend session use rejected: 0`). The trial was
reverted: the authority also refuses the lease, so bypassing the guard is not
a fix.

A traced run showed the first lease use with owner identity 1, one authority
record, token owner 1, and `retired=false`. A second call entered the same
lease method with `retired=true`, 13 apparent records, and token owner
979941777. The generic path calls `BackendSession.compile_aot_into_path` with
the same method name and arity; native receiver selection chose the lease
method for that different object layout. Renaming the lease method to
`compile_owned_aot_into_path_v2` makes the receiver unique. The next Stage4
hello run compiled, linked, and ran `Hello World` instead of rejecting the
lease. The compiler still exits nonzero at later no-op receipt publication,
tracked separately.

**Next:** run the focused lease and object-path specs, then finish the no-op
receipt fix and require a successful hello build before the matched
size/startup/RSS cohort. The trace prints were removed after diagnosis.

Evidence: `build/mini_builds/target5_stage4_k1_install.log`,
`target5_stage4_k1_hello.log`, `target5_stage4_k1_mir_build.log`,
`target5_stage4_k1_mir_hello.log`, `target5_stage4_k1_lease_build.log`, and
`target5_stage4_k1_lease_hello.log` under `build/mini_builds/`.
The receiver trace and successful hello link are in
`target5_stage4_lease_trace_hello.log` and
`target5_stage4_lease_unique_hello.log` under the same directory.
