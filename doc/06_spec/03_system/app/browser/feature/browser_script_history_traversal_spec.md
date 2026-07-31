# browser_script_history_traversal_spec

> Page-script Back and Forward traverse the canonical BrowserSession ledger and
> restore the same semantic document, browser controls, Draw IR, and Engine2D
> pixels as browser chrome traversal.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 7 | 7 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Status | Active |
| Requirements | REQ-WEB-BROWSER-004, REQ-WEB-BROWSER-009, REQ-WEB-BROWSER-012 |
| Source | `test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl` |
| Updated | 2026-07-31 |
| Render path | BrowserSession → web layout → DrawIrComposition → Engine2D |

## Scenario: restore committed pages through script history traversal

1. Enter and commit a destination.
   - Commit the green First page, enter the blue Second URL through the
     canonical address control, and submit its registered response.
2. Record the navigation entry.
   - The bounded BrowserSession ledger contains First then Second, with Second
     current at index `1` and both committed titles retained.
3. Move backward forward or stop.
   - `history.back()` restores First at index `0`; `history.forward()` restores
     Second at index `1`. Back, Forward, Stop, and address controls reflect the
     restored committed state after each move. Repeating either action at its
     stack bound is a no-op.
4. Render the restored document and controls.
   - Each batch has `html_ast` source kind. First restores a green `first`
     rectangle and Second restores a blue `second` rectangle, each at exact
     geometry `(0, 0, 16, 16)`.
   - Engine2D verifies every pixel in the 32×24 buffer: the upper-left 16×16
     region has the page color and every remaining pixel is opaque white, with
     no skipped Draw IR commands.

<details>
<summary>Executable SSpec</summary>

```simple
step("Enter and commit a destination")
# Commit First, edit the address field, and submit Second.

step("Record the navigation entry")
# Assert the two canonical entries, titles, URL, and current index.

step("Move backward forward or stop")
# Evaluate history.back() and history.forward(), then inspect browser controls.

step("Render the restored document and controls")
# Assert semantic Draw IR commands and exact Engine2D color pixels.
```

</details>

## Scenario: defer traversal requested while a page script is loading

1. `step("Commit two pages before loading a scripted destination")`
   - First and Second occupy canonical entries `0` and `1`.
2. `step("Request Back from the destination inline script")`
   - Third records `thirdRuns=1` and requests Back while its outer load is
     active; traversal remains pending rather than re-entering the loader.
3. `step("Finalize the destination before restoring the prior page")`
   - Third first commits at entry `2`, then Back restores Second at index `1`.
   - A post-restore evaluation succeeds, `thirdRuns` remains `1`, all proposal
   and pending-traversal fields are cleared, no active load remains, and the
   Third script was not replayed.

## Scenario: queue restored inline traversal without recursive ping-pong

1. `step("Commit pages whose restored scripts request opposite traversal")`
2. `step("Observe the restored request queued after the outer Back unwinds")`
   - Second requests Back once. Restored First requests Forward, which remains
     queued because the canonical Back traversal is still on the stack.
3. `step("Pump the queued Forward exactly once on the next outer operation")`
   - The next successful evaluation restores Second exactly once. Both script
     run counters are `2`, the pump guard and pending delta are clear, and no
     active load remains.

## Scenario: consume traversal once after an external script completes

1. `step("Suspend a queued Back on an external script response")`
2. `step("Complete the external script before restoring the prior page")`
   - Third commits only after the admitted JavaScript response records one
     external run; then Back restores Second with the pending delta and active
     load cleared.

## Scenario: cancel traversal queued by a replaced suspended load

1. `step("Commit two pages before a suspended scripted destination")`
2. `step("Queue Back before suspending on an external script")`
3. `step("Replace the load without consuming its stale traversal")`
   - Replacement clears the pending traversal before committing at index `2`;
     stale Back is never consumed by the new document and no active load remains.

## Scenario: clear suspended traversal on Stop and Close

1. `step("Stop one suspended traversal without navigating Back")`
2. `step("Close another suspended traversal without navigating Back")`
   - Both lifecycle owners clear the queued delta and active load. Stop retains
     the partially committed destination; Close retains no traversal work.

## Scenario: deny traversal without CSP top-navigation capability

1. `step("Load a script-enabled sandbox without top-navigation")`
2. `step("Keep the sandboxed page and clear the denied proposal")`
   - `sandbox allow-scripts` admits `history.back()` execution but the missing
     top-navigation capability keeps the sandboxed page current, emits the
     canonical warning, and clears both the proposal and pump guard.
