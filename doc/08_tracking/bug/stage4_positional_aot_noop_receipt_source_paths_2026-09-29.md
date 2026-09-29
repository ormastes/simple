# Stage4 positional AOT emits hello but cannot publish no-op receipt

- **Status:** Open
- **Found:** 2026-09-29, Linux ARM64 exact Stage4 standalone compiler
- **Impact:** compiler exits 1 after linking a runnable hello; blocks admitted
  size/startup/RSS qualification and native no-op compile cache authority

After the backend lease receiver fix, the exact Stage4 compiler compiled one
hello module, linked a 21,448-byte ARM64 executable, and that executable ran
and printed `Hello World`. The compiler nevertheless returned
`native no-op receipt publication failed: receipt-invalid` after the link.

The publication path was traced once. `native_noop_publish_fault_built_v1`
reached `native_noop_encode_v1` with `sources=0` and a nonempty request
identity. That encoder correctly refuses an empty source inventory. The
temporary print was removed. `load_sources_impl` assigns
`self.ctx.source_paths_owner` from the loaded sources, but the end-of-compile
publisher reads an empty owner vector. The exact point where it is lost is
unproven; the non-streaming `self.ctx = loaded_ctx` boundary is one candidate.

**Next:** observe the source-path owner count before/after that context
assignment and at publication, then repair the ownership transfer. Preserve
the no-op receipt's authenticated source inventory and fail-closed behavior;
do not turn off the receipt for positional AOT just to make this build green.
Then require compiler exit 0, executable output, and matched size/startup/RSS
evidence. This session stopped after three focused build/check cycles.

Evidence: `build/mini_builds/target5_stage4_lease_unique_build.log`,
`target5_stage4_lease_unique_hello.log`, and
`target5_stage4_noop_trace_hello.log`.
