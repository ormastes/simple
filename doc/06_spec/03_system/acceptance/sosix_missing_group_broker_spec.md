# Unimplemented SOSIX grouped broker development seams

Source: `test/03_system/acceptance/sosix_missing_group_broker_spec.spl`.

The host implementation slots below share the existing
`GroupProcessLauncherV1.operation` signature:
`fn(program: text, digest: text, args: [text], directory: text) -> Result<bool, text>`.
Each function currently asserts immediately with a host-specific diagnostic.
The trailing `Err` retains a fail-closed result if an execution mode removes
assertions; it does not grant a process token or claim broker ownership.

| Host | Module under `src/lib/nogc_sync_mut/io/` | Function |
| --- | --- | --- |
| Darwin/macOS | `darwin_group_broker_launcher.spl` | `darwin_group_broker_launch_v1` |
| FreeBSD | `freebsd_group_broker_launcher.spl` | `freebsd_group_broker_launch_v1` |
| illumos | `illumos_group_broker_launcher.spl` | `illumos_group_broker_launch_v1` |

These are unregistered development placeholders. Existing Linux and Windows
launchers and their registration remain unchanged. No existing portable capture,
spawn, executable lookup, snapshot or unavailable-capability behavior changes.
Host owners must supply actual executable identity, descendant lifetime and
memory evidence before a grouped provider can be registered or advertised.

## Executable cases

1. Call the Darwin placeholder in an isolated child.
2. Call the FreeBSD placeholder in an isolated child.
3. Call the illumos placeholder in an isolated child.

Each case requires a nonzero child exit, an assertion failure, the exact missing
host diagnostic, and absence of the marker printed after the call returns.
A missing import, ordinary unsupported result, or fabricated success cannot pass.

Set `SIMPLE_BIN` to the same admitted executable used for the outer SSpec runner.
Run `simple test test/03_system/acceptance/sosix_missing_group_broker_spec.spl`.

## Recorded evidence

On 2026-10-29 the pinned P1 bootstrap interpreter diagnostic ran three cases:
all three failed before the functions existed; all three passed with the assertion
bodies. This is seed diagnostic evidence only, not self-hosted/native execution
qualification or evidence of any host's grouped process capability. P2 was not
rebuilt. The child runtime reports assertion failures through its interpreter
fallback; no native backend claim is made.

The final three-case check, including the explicit `assertion failed` matcher,
used `/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple`, SHA-256
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`.
This differs from the initial pinned P1 generation, which was removed by
concurrent workspace cleanup after the first red/green diagnostic run.
