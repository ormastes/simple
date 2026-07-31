# Stop Preserves Partial Document Focus

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Category | Browser Stop lifecycle and retained page state |
| Status | Static candidate; runtime and docgen not run |
| Requirements | REQ-WEB-BROWSER-008, REQ-WEB-BROWSER-009, REQ-WEB-BROWSER-021 |
| Executable source | `test/03_system/app/browser/feature/browser_stop_partial_focus_spec.spl` |
| Plan | `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md` |
| Evidence | Visible partial DOM, focused target, UTF-8 selection, chrome cleanup, and capability retirement |

## Scenario

### should retain focus and selection while retiring transient state

1. **Open the same partial document in hosted and isolated renderers**
   - Both routes expose the same focused text input and visible body while an
     external stylesheet remains pending.
   - Stop is enabled in both `BrowserSession` instances.
2. **Retain page selection while transient chrome state is armed**
   - Both inputs select bytes 1 through 5 of multibyte `pärtial` on valid
     UTF-8 boundaries.
   - The isolated route also carries page-view, pressed-target, chrome-focus,
     and address-replacement state before Stop.
3. **Activate Stop through hosted chrome and isolated authority**
   - The hosted release invokes the public Stop chrome action.
   - The isolated route admits a capability-bound `navigation/stop` command.
4. **Observe partial focus and selection with transient state retired**
   - Both visible partial documents retain focused target `draft` and the
     exact byte selection.
   - Press/chrome state is empty, the isolated page view remains intact, and
     root-command/capability authority is retired.

## Failure Discrimination

| Observation | Failure |
|---|---|
| visible body disappears | Stop replaced rather than retained the partial document |
| hosted focus survives but isolated focus is empty | isolated navigation cleanup ran replacement policy for Stop |
| selection becomes `0..0` | Stop discarded live page editing state |
| pressed/chrome state remains | Stop retained transient host ownership |
| command capability remains non-empty | terminal renderer authority was not retired |

## Traceability

| Requirement | Executable evidence | Manual evidence |
|---|---|---|
| REQ-WEB-BROWSER-008 | hosted and isolated routes retain identical DOM focus and byte selection | four-step parity observation |
| REQ-WEB-BROWSER-009 | public chrome release and capability-bound renderer command both execute Stop | explicit Stop activation step |
| REQ-WEB-BROWSER-021 | partial content is retained while transient chrome and command authority clear | final lifecycle assertions and failure table |

## Provenance

This page was hand-reconciled with the executable scenario because the bounded
lane forbids runtime and docgen execution. It makes no runtime PASS claim. The
executable SSpec remains the authoritative assertion source.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
