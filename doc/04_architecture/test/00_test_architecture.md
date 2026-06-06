# Test Architecture

This is the entrypoint for Simple test architecture. It covers SPipe specs,
the test runner, markdown/documentation tests, comment-based test controls,
Sdoctest, and remote/bare-metal execution lanes.

## Scope

The test architecture owns how test intent is discovered, scheduled, executed,
reported, and converted into documentation evidence. It spans local `.spl`
SPipe specs, `.spipe` scenario files, markdown doctests, Sdoctest blocks,
generated spec docs, QEMU/bare-metal remotes, GUI/container adapters, and
resource-governed daemon scheduling.

## Execution Flow

```text
test source
  -> manifest scan
  -> preprocess SPipe / doctest / Sdoctest
  -> schedule through direct runner or test daemon
  -> adapter: local, container, QEMU, hardware, remote PC, GUI
  -> result records
  -> doc generation / tracking DB / verify gates
```

## Test Families

| Family | Source | Primary code |
|--------|--------|--------------|
| SPipe specs | `test/**/*.spl`, `.spipe` scenarios | `src/app/test_runner_new/*` |
| SSpec wrappers | wrapped spec execution files | `test_runner_execute.spl`, `test_runner_main.spl` |
| Markdown doctest | fenced code in markdown | `doctest_runner` exports |
| Sdoctest | markdown interactive blocks and comments | `src/app/test_runner_new/sdoctest/*` |
| Comment controls | `<!--sdoctest:...-->`, tags, skip/ignore markers | `sdoctest/extractor.spl` |
| Remote/bare-metal | QEMU, hardware, remote PC, T32/serial lanes | `src/app/test_daemon/adapters/*` |
| UI tests | SGTTI and `/api/test/*` assertions | `../ui/ui_test_architecture.md` |

## Bare-Metal And Remote Lane

```text
system spec
  -> target metadata
  -> test daemon session scheduler
  -> qemu_adapter / hardware_adapter / remote_pc_adapter
  -> boot/upload/run/collect logs
  -> SPipe assertion result + evidence doc
```

Bare-metal remote tests must keep target setup, upload, execution, and evidence
collection visible in the spec or adapter result. The runner should queue or
reuse warm sessions through the daemon when resource policy says the host is
under pressure.

## Documentation Test Lane

```text
markdown file
  -> discover code fence or sdoctest block
  -> apply comment modifiers and environment config
  -> build temporary Simple source
  -> run with selected timeout/env
  -> write result DB and generated report
```

Comment controls are part of the test contract. They may skip, ignore,
mark expected failure, select environment, attach tags, or choose run config,
but they must remain visible in the source document.

## Invariants

- Generated executable specs never live under `doc/06_spec`; that tree stores
  generated/manual markdown evidence.
- Placeholder passes (`pass_todo`, empty bodies, trivial true assertions) are
  verify failures.
- The daemon is a scheduler/control plane. Specs remain separately accountable
  even when they share QEMU or remote sessions.
- Remote and bare-metal adapters must report enough target, command, and log
  location data for a failed run to be reproduced.

## Detailed Docs

- `test_runner_daemon_resource_governor.md`
- `../ui/ui_test_architecture.md`
- `../../07_guide/app/lsp_dap/lsp_dap.md`
- `../../07_guide/compiler/backends/baremetal.md`

