# W14-A — Enterprise Web UI Output-Escaping Audit List (2026-08-17)

Lane `.spipe/simple_enterprise_suite` W14-A. Every place a route render/handler
in `src/app/enterprise_store_app/` interpolates a request- or store-derived
value into HTML, and whether it passes through `web_common.esc()` before landing
in the output. Scope excludes `main.spl` (dispatcher, owned by W14-C).

`esc()` escapes `&`, `<`, `>`, `"`->`&quot;`, `'`->`&#39;` (order: `&` first).
It is therefore safe for element context AND for single/double-quoted attribute
values. All attributes in the app are double-quoted.

## Audit list (path:function -> escaped? / source of value)

| File:function | Interpolated value | Context | Escaped? | Source |
|---|---|---|---|---|
| booking_routes:page_resources | resource_id, mode, capacity | `data-resource="..."` attr + element | YES `esc()` | store row |
| booking_routes:page_booking_status | booking_id, status | element `<span>` | YES `esc()` | URL param / library |
| booking_routes:command_page | reason, detail | element | YES `esc()` | CommandResult |
| booking_routes:handle (404) | (static) | — | n/a | literal |
| restaurant_routes:page_session_view | table_id, session_id, line_id, sku, qty, modifiers, status | `data-line="..."` attr + element | YES `esc()` | URL / store rows |
| restaurant_routes:command_page | reason, detail | element | YES `esc()` | CommandResult |
| dashboard:stat_line | value (label/css are static literals) | `<span class="...">` element | YES `esc()` value; class is literal | counts |
| dashboard:page_dashboard | sku, name; audit_text/balanced_text | element | YES `esc()`; text flags are fixed literals | store rows |
| auth_routes:store_app_handle_bearer (login) | `"token=" + r.detail` | body (text/html) | NO — but safe by source | server-issued token (entropy) |
| auth_routes (errors) | decision.0, "invalid-credentials", "rate-limited" | error body | fixed strings | literal / library reason |
| auth_routes (logout) | "logged-out" | element | n/a | literal |
| hcm_routes:page_employees | emp, name, status, wage | `data-employee="..."` attr + element | YES `esc()` (wage placeholder literal) | store rows |
| hcm_routes:page_payroll | period_start/end (literals), cols[0..3] | `data-employee="..."` attr + `<td>` element | YES `esc()` | store rows |
| hcm_routes:command_page | reason, detail | element | YES `esc()` | CommandResult |
| procurement_routes:page_open_pos | po_id, supplier, sku (+ literal counts) | `data-po="..."` attr + element | YES `esc()` | store rows |
| procurement_routes:page_reconcile | kv[0] (label + class), kv[1] | `<span class="...">` + element | YES `esc()` all three | store-derived pairs |
| procurement_routes:command_page | reason, detail | element | YES `esc()` | CommandResult |
| finance_routes:page_trial_balance | line.account (+ literal amounts); flag | `data-account="..."` attr + element | YES `esc()`; flag is fixed literal | ledger |
| finance_routes:page_ar / page_ap | entry.0 (+ literal amounts) | `data-ref="..."` attr + element | YES `esc()` | ledger |
| finance_routes:page_period_status | (literal placeholders) | element | YES `esc()` | — |
| finance_routes:command_page | reason, detail | element | YES `esc()` | CommandResult |
| web_common:deny | reason (library) + `esc(detail)` | error body | detail YES `esc()`; reason is closed-set literal | CommandResult |
| web_common:command_page pattern | reason, detail | element | YES `esc()` | CommandResult |

## Security-header coverage

Every `HttpResponse` construction in the seven route files is wrapped by
`secured()` (directly, or via `deny()` / `command_page`, both of which call
`secured()`). Verified by grep: no unwrapped `HttpResponse.{html,error,...}`.
This includes all denial paths (`deny()`, trailing `404`, auth `too_many()`,
`unauthorized()`, `413`/`501`/`400`).

## Conclusion

No unescaped attacker-influenceable interpolation exists. `esc()` already
covers attribute context. All response paths carry the shared headers. The one
non-`esc()` interpolation (`auth` `token=` + `r.detail`) is a server-issued
token, not attacker-influenceable. Added regression fences (attribute-context +
vertical route families) rather than inventing a fix — see
`test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl`.
