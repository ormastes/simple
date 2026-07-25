<!-- codex-research -->
# Domain Research: UI CLI LLM Access

## Official TRACE32 behavior

Lauterbach documents `t32rem` as an external-shell CLI over its Remote API. Remote control must be enabled; PRACTICE scripts may return immediately or be bounded by an explicit wait. The API controls PowerView over sockets, reports communication and command-rejection failures distinctly, and requires callers to poll PRACTICE state. State `2` means a dialog is open, which supports an explicit `interaction_required` result instead of blind waiting. Sources: [t32rem knowledge base](https://support.lauterbach.com/kb/articles/how-to-use-the-t32rem-tool), [Remote API manual](https://www2.lauterbach.com/pdf/api_remote_c.pdf).

Live windows can be discovered with `WINdow.LIST()` and queried with `WINdow.POSition()`. Names can be duplicated and user-defined, are case-sensitive, and list order follows changing Z-order. Therefore window name is not a stable identity and output needs common-layer deterministic ordering. Sources: [TRACE32 function reference](https://www2.lauterbach.com/pdf/ide_func.pdf), [TRACE32 command reference](https://www2.lauterbach.com/pdf/ide_ref.pdf).

Official capture paths include `PRinTer.FILE` with `WinPrint` for text and `SCreenShot` for images. Hidden modes have different dialog behavior. TRACE32 `HISTory` covers typed command-line entries while `LOG` records a different replayable stream; neither is a complete per-target LLM action/result audit. Sources: [window text capture](https://support.lauterbach.com/kb/articles/how-can-i-print-the-content-of-a-trace32-window-into-a-file), [displayed value evaluation](https://support.lauterbach.com/kb/articles/how-can-i-evaluate-values-displayed-within-a-trace32-window-in-a-practice-script), [hidden instances](https://support.lauterbach.com/kb/articles/how-do-i-start-a-hidden-instance-of-trace32), [user guide](https://www2.lauterbach.com/pdf/ide_user.pdf).

## Cross-platform semantic access principles

WAI-ARIA represents interfaces as roles, states, properties, and relationships in an accessibility tree. This supports one renderer-neutral GUI/TUI semantic schema, with adapters producing the tree rather than CLI code scraping pixels. [WAI-ARIA 1.2](https://www.w3.org/TR/wai-aria/).

Identity must be opaque, scoped, and stale-detectable. Windows UI Automation prefers stable automation IDs where available but treats runtime IDs as opaque and desktop-scoped. WebDriver BiDi uses shared references and a typed `no such node` failure. Sources: [UI Automation testing guidance](https://learn.microsoft.com/en-us/windows/win32/winauto/uiauto-usefortesting), [WebDriver BiDi shared references](https://www.w3.org/TR/webdriver-bidi/#type-script-SharedReference), [WebDriver BiDi errors](https://www.w3.org/TR/webdriver-bidi/#errors).

Actions must be capability-driven. UI Automation exposes supported control patterns; AT-SPI exposes named actions and recommends semantic actions over synthetic pointer events. A CLI must query advertised actions and state rather than infer clickability from role or text. Sources: [Microsoft control patterns](https://learn.microsoft.com/en-us/windows/apps/design/accessibility/control-patterns-and-interfaces), [AT-SPI Action](https://gnome.pages.gitlab.gnome.org/at-spi2-core/libatspi/iface.Action.html).

Platforms distinguish unavailable, disabled, busy/defunct, unsupported, and cannot-complete states. Those must remain distinct rather than becoming an empty result or generic error. Sources: [UI Automation supported patterns](https://learn.microsoft.com/en-us/dotnet/framework/ui-automation/get-supported-ui-automation-control-patterns), [Apple AXError](https://developer.apple.com/documentation/applicationservices/axerror), [AT-SPI states](https://gnome.pages.gitlab.gnome.org/at-spi2-core/libatspi/enum.StateType.html).

## Structured CLI and agent safety

RFC 8259 requires interoperable JSON object names to be unique and JSON exchanged across systems to use UTF-8. Array ordering is meaningful; object-member ordering is not. Bound list size, depth, text, and history, and expose truncation explicitly. [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259.html).

JSON Schema Draft 2020-12 supports a declared machine contract. The payload should carry its own protocol/schema version; compatible changes should be additive, with breaking meaning/type changes reserved for a major version. [JSON Schema Draft 2020-12](https://json-schema.org/draft/2020-12).

MCP tools pair JSON Schema with structured results and distinguish protocol/request faults from actionable tool failures. Tool annotations include read-only, destructive, idempotent, and open-world hints, but servers still validate inputs and enforce policy. This supports read-only list/snapshot/find and separately capability-checked action operations with confirmation eligibility. [MCP tools specification](https://modelcontextprotocol.io/specification/2025-11-25/server/tools), [MCP security guidance](https://modelcontextprotocol.io/docs/tutorials/security/security_best_practices).

POSIX uses exit `0` for success and nonzero for failure, with diagnostics on standard error. Machine mode should keep standard output to the documented payload and exclude progress/log noise. [POSIX utility conventions](https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/utilities/command.html).

## Design inferences for Simple

These are synthesis choices, not guarantees made by the cited standards:

- Canonical identity should include source/session scope, surface ID, opaque node ID, and snapshot revision/generation. An action re-resolves against the current revision and returns `stale_target` rather than acting on a reused ID.
- TUI should expose the same semantic contract directly from retained UI state; ARIA does not govern terminal applications.
- `find` operates on a bounded snapshot. `act` re-resolves, checks advertised capability and enabled/busy/defunct state, invokes the owning adapter, appends a correlated result event, and refreshes/observes.
- Preserve typed errors such as `source_unavailable`, `interaction_required`, `permission_denied`, `unsupported_action`, `target_not_found`, `stale_target`, `target_disabled`, `target_busy`, `timeout`, and `invalid_argument`.
- Use stable application ordering and semantic JSON assertions. RFC 8785 canonical byte serialization is unnecessary unless signing/hashing becomes a selected requirement.

## Primary-model review

The three domain threads agree with the local architecture: one semantic model, source-owned adapters, explicit capabilities/staleness, bounded history, and deterministic structured CLI output. The primary model rejects two tempting shortcuts: using display names as IDs and silently falling back from semantic actions to lower-confidence raw input.

