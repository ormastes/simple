# Hosted WM Live-Proof Focus Contract

Executable spec:
`test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl`

## Purpose

The Linux hosted-WM live evidence sends a real Tab key and requires the focused
internal window ID to change. The live-proof scene therefore needs two real
windows. This contract keeps the deterministic `Files` peer before `Terminal`,
so creation leaves `Terminal` focused and Tab wraps to `Files`.

The windows remain normal `HostCompositor` lifecycle objects projected through
`SharedWmScene`, `DrawIrComposition`, and Engine2D. No alternate input or render
route is introduced.

## Scenarios

### Seed the focus peer before Terminal

1. Read `_seed_live_proof_surface` from the production hosted entry.
2. Confirm both `Files` and `Terminal` use the existing bridge-window path.
3. Confirm `Files` is created first and `Terminal` last.

Expected result: initial focus belongs to `Terminal`; canonical focus cycling
has a distinct peer to select.

### Preserve normal startup

1. Read `_run_hosted_wm`.
2. Confirm live-proof mode uses `_seed_live_proof_surface`.
3. Confirm the normal branch still uses `_seed_host_compositor_shared_mdi`.

Expected result: normal hosted-WM startup behavior is unchanged.

### Deliver Tab through the canonical focus operation

1. Confirm native `KEY_TAB` dispatch calls `host_compositor_cycle_focus`.
2. Inspect that shared operation in `host_compositor_core.spl`.
3. Confirm it advances to the next window and focuses that window ID.

Expected result: the wrapper's before/after focus-ID comparison proves both
native key delivery and a real compositor state transition.

### Restore the same focused proof window

1. Inspect the existing evidence-command `restore` branch.
2. Confirm it resolves the focused window ID.
3. Confirm it restores that window rather than every internal window.

Expected result: maximize/restore returns the two-window array byte-for-byte to
its pre-maximize focus, geometry, minimized, and maximized state. The normal
R-key path retains its existing restore-all behavior.

## Static reproduction

```sh
bin/simple test test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl --mode=interpreter
```

The live X11 evidence wrapper remains the runtime acceptance gate; this focused
spec protects the production source contract without replacing that gate.
