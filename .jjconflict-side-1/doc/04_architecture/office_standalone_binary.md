<!-- codex-architecture -->
# Standalone Office Binary Architecture

## Decision

Office Calc is an independently compiled application target. The portable core
owns sheet state, formulas, canonical 20×30 layout, and deterministic frame
construction. Platform adapters own process arguments, terminal input, and OS
launch integration.

```text
spreadsheet/formula + common spreadsheet layout
                    |
                 calc_tui
                 /       \
       calc_tui_host   SimpleOS office_calc entry
              |                  |
      office_cli/main       frame output now;
      macOS native app      OS UI/TTY adapter later
```

`office/mod.spl` remains the broad suite/plugin owner and is not a native Calc
build entry. `simple office` compatibility may delegate to a cached `office`
artifact later, but must not restore raw-source execution.

## Build and startup

The build uses self-hosted `native-build`, explicit entry closure, and the
normal hosted runtime bundle. The resulting executable starts directly; it has
no compiler or bootstrap path. SimpleOS uses a distinct static target link with
the same core and an OS-specific entry.

## State and layout

`common.ui.spreadsheet_grid` owns viewport dimensions and grid metrics. Calc TUI
uses those semantics instead of private 20×30 arithmetic. Web/GUI producers can
lower the same canonical metrics through their platform layout adapters without
depending on terminal padding.

## Target limitation

The current SimpleOS `simple-core` archive lacks runtime symbols required by the
Calc closure, and ring-3 lacks interactive terminal control. Both conditions are
explicit platform prerequisites. Office does not bootstrap around them.

## Consequences

- Host launch is small, deterministic, and independent of the monolithic Office
  GUI closure.
- SimpleOS can share formulas/layout without importing hosted TCP or termios.
- Packaging must produce one artifact per target.
- Full SimpleOS interactive acceptance waits for its runtime and terminal ABI.
