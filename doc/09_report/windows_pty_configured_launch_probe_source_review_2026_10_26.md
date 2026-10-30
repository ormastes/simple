# Configured PTY startup probe: independent source review

Date: 2026-10-26. Reviewer: Astra independent audit lane.
Workspace: D:/dev/simple-coremux-shared-20261025.
Observed HEAD: 42690d6342b55c997efebb54a8508cc9921c0ae6.
Reviewed delta: 9ce3db18d9b7c61c80c4aba1447a7969afb0f019 to
bae69fc813b6ca74c0449f92666e6d89c81647d1, restricted to the six paths below.
Current bytes have no diff from the latter commit for these paths.

STATUS: WARN / source review accepted; native execution NOT_RUN.
No concrete scoped P0/P1/P2 finding was identified.
No build, test, compiler, helper, native fixture or product was launched.
No production code was edited and no commit was made.

## Exact input pins

| Path | SHA256 |
| --- | --- |
| src/lib/sys/pty.spl | 45f2b299581e1fdf64405eef862646b83b0ba8a5bb189985629f6a8fc90fbc09 |
| src/lib/nogc_sync_mut/sosix/pty.spl | c7f5b9515baef233c13fbb4d8a055d01895392d972f86987500f63c43519556e |
| src/lib/nogc_async_mut/sosix/pty.spl | 8b78d97a69562a74085a6d9d3b49f3a467958bb1fa9d923b61b8f597ab6df103 |
| src/providers/windows_native/lib/sys/pty.spl | 0c904d9db01a87aeebcbd16b5dd07338e384cb1f6062362b80549775dad551fb |
| test/fixtures/compiler_entrypoint/windows_pty_launch_probe/main.spl | 2581f543873fa7d7c1c07b2b555c5f405a14e07fa294ed3a417f0e19c2a17e77 |
| doc/09_report/coremux_windows_pty_launch_probe_source_2026_10_25.md | 346b104adec61ca03571221585a5cf09ca090f5cd191a4486e3f96c19a81d4f9 |

## Source conclusions

The generic Sys facade explicitly returns false. Its legacy ABI cannot carry
the configured launch value. Both existing SOSIX facades forward the same
provider-selected symbol; no directory name, function-presence heuristic,
basic PTY availability or resize capability is used to infer support.

The Windows overlay invokes actual open(1,1), returns false for failed open,
then calls close and cleanup_proof exactly once for a successful open. Both
results must be true. It neither retries nor memoizes globally. This is a
startup effect with real resource acquisition, not a pure capability query.
It launches no child, changes no parent environment/cwd, and introduces no
new native binding.

The existing reviewed owner contract retains failed cleanup authority in the
native registry/quarantine. False therefore cannot be treated as a clean-drain
receipt. The probe does not drop a retained record or reset/reuse its handle.
A successful probe consumes one nonreused lifetime slot and releases its active
resources. These conclusions use the previously reviewed owner contract; this
small review did not repeat the launch-owner implementation audit.

The authored native fixture obtains its parent environment baseline before
the single probe, retains its result, and requires both success and zero pending
cleanup. Its final environment comparison includes the probe interval. Existing
child and cleanup assertions remain strict. This is meaningful source coverage,
not executed evidence.

## Explicit integration boundary

The documentation requires exactly one probe per configured server-owner startup,
storage of that observation, discovery reuse, and failed admission on false.
Those server lifecycle rules are not implemented or proven by this six-file delta.
The probe is intentionally callable and does not itself enforce once-per-owner
use. A later server integration review must verify the actual call site, stored
state, refusal path and cleanup ownership; repeated discovery must not allocate
additional tombstones.

Success establishes selected-provider/basic ConPTY prerequisite availability,
not successful configured child creation, environment merging, cwd selection,
quoting, Job admission or future allocation. Later launch errors must remain
normal typed failures. The native fixture and all previously listed configured
launch qualification gates remain NOT_RUN. Failed open/close native fault
injection, generic-negative execution and server lifecycle execution remain
required; no provider admission or full CoreMux readiness is asserted.

## Preserved prior review

The configured-launch v2 source review and its historical pins remain unchanged
in windows_pty_configured_launch_source_review_2026_10_25.md
(SHA256 b5b90061a975c7b6ea66a49867eff7c5f7c7ff2d7a8f8c9a8e11aa362085aca5).
Its close-completion and linear strict UTF8 corrections are not reclassified as
native PASS. This separate report records only the additive startup-probe delta.
