# Windows native-build rejects a renamed running compiler

Source 93f7, run 45357104625, Windows P3a job 138317543998, failed before
creating its worker ledger. The retained stage3-a.log contains
`[capsule-shard] disabled: running compiler path unavailable` followed by the
explicit refusal to fall back from the selected per-file route.

The actual producer was the verified `simple_stage2.exe` from run 45346335752,
SHA f8be04ff2979d4b41cd038f8aa3601619891ec7cf74b55dbe73f06c84baa85f0.
`native_build_main.spl::self_exe` accepted argv[0] only when it ended in
`/simple` or `simple.exe`; this excluded the actual basename. Its later shell
queries did not recover a usable path in this run. The log does not identify
which individual fallback failed. SIMPLE_BINARY was correctly set by the
wrapper but intentionally cannot authorize another compiler for shard work.

The Windows branch now uses the runtime-platform-backed `host_is_windows_host`
predicate and calls the existing `cli_kernel_executable_path` owner.
That owner obtains the current image via GetModuleFileNameW and validates the
path. It does not trust argv or environment values, and an unavailable kernel
identity still fails closed. Linux and macOS behavior is unchanged.

Focused verification uses the actual canonical lookup in a native Windows
fixture renamed to simple_stage2.exe, with spoofed argv[0] and stale configured
compiler paths. Its seven assertions require a real Windows host, a nonempty
existing image, the renamed basename, and SHA-256 equality with the collector's
independent hash. The collector also verifies the production Windows call-site
change and unchanged non-Windows body. This proves the lookup and source wiring;
it is not a rebuilt full native_build_main or completed P3a qualification.

Initial native proof 45363000685 passed seven assertions under the ordinary OS
profile, with a renamed PE, spoofed argv and stale compiler environment values.
The native fixture SHA was
4309dabe73d9cc72cad8a278ceec4d3d4ebad4977208c07f239304d3464eb8af;
both compile and execution owners completed with exit 0 and quiescence.
Review then identified that the initial `host_os()` selector depended on the
ambient OS variable. The runtime-backed predicate corrects that selector;
the additional OS-unset and spoofed profiles require their own native evidence.
The first passing case is retained and is not repeated.
The failed P3a generation is retained unchanged and is not retried by this fix.
