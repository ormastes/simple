# Configured PTY launch composition: source candidate

Status: **WARN / NOT_RUN**. Nine pure admission cases and two actual-child cases authored; zero executed. The child fixture is **NOT_BUILT**. Independent review is pending. No build, compiler, native helper, product or SSpec launch occurred. No API, existing pane I/O, WPL, system-provider, or common-validation owner was edited.

Approved interface: `pane_spawn_configured_pty_state(before: ServiceState, closing: bool, session_id: text, window_id: text, pane_id: text, launch: SosixPtyLaunchV1) -> PanePidUpdate`. The local type name aliases existing `std.sosix.pty.PtyLaunchV1`; no new public launch ABI is introduced.

## Authority and failure contract

The API remains the sole state publisher. The adapter must validate common `MuxLaunchV1` before lossless mapping, pass the real closing/quarantine policy, reserve operation/configuration identity, and publish the returned state exactly once when `commit` is true. `cleanup_pending` must be honored even when `commit` is false. This lower owner does not establish complete generic launch validity or full CoreMux capability admission.

The actual effect function uses a production pure admission helper for all three ancestry identities, existing child/deferred handle refusal, `can_attach`, positive dimensions at most 32767 each and grid area at most 262144. Multiplication occurs only after individual bounds. Both content and incarnation counters have capacity before any allocation. Exec/Shell, argv, cwd, and Set/Remove values reach the selected configured provider unchanged; there is no new parser, quoting policy, shell prefix, local process registry, platform branch, or pipe fallback.

Provider validation remains platform-owned. Opening a PTY may therefore precede a platform-specific refusal. Provider error strings are not surfaced because they may contain argv, cwd or environment data. A provider Err or nonpositive PID leads to checked close. Close=false commits the exact fd with PID=-1 using existing `with_pty`, consuming its reserved incarnation and retaining the previous content for later checked cleanup. Close=true returns the original state. Positive PID commits the existing owner transform, preserving its counter/content semantics; it is not a claim of externally observed Running state.

Negative open can leave provider-global quarantine without returning an addressable fd. The new owner queries generic `sosix_pty_cleanup_pending`; every nonzero result, including unknown/sticky -1, reports pending without inventing a pane token or a state commit. No before/after count subtraction claims per-request attribution. The server must preserve its provider-wide stop/cleanup gate and cannot delegate foreign cleanup authority to this pane caller.

## Reused owners and bounded evidence

Existing `PanePidUpdate`, `PaneRecord.can_attach/with_pty`, `pane_capture_state`, and `close_owned_children` are reused. No helper body was extracted or duplicated from an existing native provider. Pure tests use explicit records only, including clearly synthetic ownership tokens that never reach native calls. Actual-child tests use real returned PIDs/fds, child-computed argv/environment/cwd evidence, bounded lifetime/capture/cleanup, overwrite refusal, independent process-presence checks, and global pending status. They clean before assertions and retain any distinct second returned state if overwrite refusal regresses.

The native cases have no deterministic failed-close injection, no native execution at counter exhaustion, and no proven Job/resource receipt yet. Neither pure admission nor authored native code establishes OS effect ordering, provider correctness, public API wiring, all 39 mandatory CoreMux operations, or capability qualification. Root owns the eventual API hook and adapter mapping; this isolated explicit-state owner is not yet a connected public launch command.

## Concrete adjacent gaps retained outside this lane

- Existing `pane_io_service.pane_spawn_pty_state` previously reported `cleanup_pending: false` when `pty_open` returned negative. The Windows owner `_windows_pty_open_failed_v1` can retain provider-global quarantine before returning -1. Root separately source-corrected the legacy branch using the same generic pending query; that owner was not edited or included in this lane's freeze. Its independent review is pending, and native refusal/quarantine fault tests remain NOT_RUN. Neither branch invents a pane token or per-request attribution from global status.
- `std.sosix.environment` has a checked implementation in `src/lib/nogc_async_mut/sosix/environment.spl`, but no corresponding `src/lib/nogc_sync_mut/sosix/environment.spl`. Strict configured sync resolution therefore cannot simply import that generic environment owner. Root explicitly approved existing `app.io.mod` env/cwd facade fallback in the test and child fixture. The code adds no raw extern or runtime leaf call and no cross-family alias. A generic common owner extraction requires separate review; this lane does not expand library-family resolution.

Exact candidate paths and hashes are retained in `build/review/smux-configured-launch-source-v1.sdn`. Runtime qualification and generated-manual checks remain pending.
