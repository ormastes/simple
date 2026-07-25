# Test Architecture

This is the entrypoint for Simple test architecture. It covers SSpec `.spl`
specs, the SPipe runner/docgen process around those specs, scenario manuals,
markdown/documentation tests, comment-based test controls, Sdoctest, and
remote/bare-metal execution lanes.

## Scope

The test architecture owns how test intent is discovered, scheduled, executed,
reported, and converted into documentation evidence. It spans local SSpec
`.spl` specs, generated SSpec scenario manuals, markdown doctests, Sdoctest
blocks, generated spec docs, QEMU/bare-metal remotes, GUI/container adapters,
and resource-governed daemon scheduling.

## Execution Flow

```text
test source
  -> manifest scan
  -> preprocess SSpec / doctest / Sdoctest
  -> schedule through direct runner or test daemon
  -> adapter: local, container, QEMU, hardware, remote PC, GUI
  -> result records
  -> doc generation / tracking DB / verify gates
```

## Test Families

| Family | Source | Primary code |
|--------|--------|--------------|
| SSpec specs | `test/**/*.spl` | `src/app/test_runner_new/*` |
| SSpec scenario manuals | `test/**/*_spec.spl` with `step("...")` manual steps | `src/app/spipe_docgen/*` |
| SPipe process state | `.spipe/**` process/control files | `.spipe/**`, SPipe orchestration |
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
  -> SSpec assertion result + evidence doc
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

## SSpec Scenario Manual Lane

SSpec scenario manuals are executable `.spl` specs that generate
human-readable manuals under `doc/06_spec`. SPipe is the process/tooling around
running those specs and generating manuals; it is not a separate `.spipe`
scenario source format.

Current SSpec manuals use explicit step text as the primary source of manual
actions:

```simple
use std.spec.*

describe "Dashboard actions":
    # @inline
    it "operator has an authenticated session":
        step("Open the sign-in page")
        step("Submit valid credentials")

    it "operator reviews dashboard actions":
        # @include("operator has an authenticated session")
        step("Open the actions panel")
        expect("actions").to_equal("actions")
```

Generated manual steps are compact and contiguous:

```md
1. Open the sign-in page
2. Submit valid credentials
3. Open the actions panel
   - Expected: "actions" equals `actions`
```

`Given_*`, `When_*`, and `Then_*` helper naming is legacy style. Keep it only
when maintaining older specs; new SSpec manuals should use `step("...")`.
See `../../07_guide/infra/sspec_scenario_manual.md`.

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
- `../../07_guide/infra/sspec_scenario_manual.md`
- `../../07_guide/app/lsp_dap/lsp_dap.md`
- `../../07_guide/compiler/backends/baremetal.md`
