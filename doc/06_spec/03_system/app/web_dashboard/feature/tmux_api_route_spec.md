# Dashboard tmux HTTP route

Source: test/03_system/app/web_dashboard/feature/tmux_api_route_spec.spl.
Trace: REQ-CMUX-001/003/005/008/010; application inventory A06/A07.
Status: **NOT_RUN**. Twelve authored cases; zero executed. This authored mirror
is not generated evidence. Matching full CLI, spec-maintain and docgen remain
pending. No Phase2/seed substitute or inference of IDE/smux parity is allowed.

## Protocol controls

The protocol scenarios call the production handler and HTTP response formatter,
with separate controls on DashboardServer's actual authentication/origin gates.
They cover authentication, exact route boundaries, 404/405 before backend access, malformed
and duplicate JSON, invalid numeric fields, strict percent/UTF8 decoding,
NUL/C1 target rejection, literal-versus-key ambiguity and body bounds. These are
protocol controls only, not proof that tmux is installed or that a child ran.
Fabricated session strings are not used to bypass the live-session lookup.
Two additional pure controls exercise the production argv encoder and session
wire parser; these are not fake provider executions or multi-client runtime proof.

## Real host scenario

The final scenario launches a compiled product binary for
src/app/dashboard/web_entry.spl, opens real TCP connections, and requires:

1. Actual operator login over HTTP and the returned opaque session cookie,
   followed by HTTP 201 creating a unique session and a real list containing its
   exact name. Repeat for names ending in `;` and `\;`.
2. Actual window/pane indexes, followed by a command sent to the child shell.
3. A captured standalone `DASHBOARD_HTTP_CHILD_OK_한😀` output line, distinct
   from the echoed command. JSON and HTTP preserve its UTF8 byte framing.
4. Two real control-mode clients attach; an independent tmux format reports at
   least two clients while HTTP session listing succeeds with `attached:true`.
   Both client processes are then closed before continuing the pane exercise.
5. The child executes `read -r` and prints distinct oracle lines for `;`,
   `hello;`, one/two backslashes before `;`, a trailing backslash and Unicode
   ending in `;`. Captured shell-command echo cannot satisfy the line oracle.
6. A controlled three-pane layout gives the target neighbours on both axes.
   HTTP resize must produce an independently observed 70x20 target pane, followed
   by DELETE with its JSON body transmitted over TCP.
7. Session disappearance proved by a successful checked inventory that still
   contains a separate live, uniquely owned guard session and excludes the
   deleted target. A query error is never interpreted as absence.
8. Recorded child/control/dashboard PID termination and all cleanup outcomes
   before the final exact success marker assertion. Guard creation and each
   split retain their child PID directly from tmux's creation response; HTTP
   session creation is immediately followed by checked child inventory.

The fixture coordinator must supply an admitted, hashed product executable in
SIMPLE_TEST_WEB_DASHBOARD_EXE and a private unused port in
SIMPLE_TEST_WEB_DASHBOARD_PORT. Record producer/source/runtime/target and Hello
admission externally before running; an environment path alone is not admission.
SIMPLE_TEST_TMUX_ROOT must name a newly owned private tmux directory, equal to
TMUX_TMPDIR, with an isolated configured tmux server and POSIX child shell.
Unset TMUX so an inherited client socket cannot override the private directory.
Set SIMPLE_TEST_TMUX_SHELL=posix only after verifying that fixture. Supply the
private SDN verifier via DASH_AUTH_FILE and matching fixture-only credentials
via SIMPLE_TEST_DASHBOARD_USERNAME and SIMPLE_TEST_DASHBOARD_PASSWORD. See the
web_login auth manual for provisioning. Never log plaintext credentials or
cookies. The spec performs real POST /login and passes its cookie with the exact
loopback Host/Origin; DASH_AUTH cannot disable mux authentication. The server
binds loopback only. The coordinator owns removal of the private server/directory;
the spec kills only its uniquely named target/guard sessions and its own piped
dashboard/control clients. Its bounded cleanup ledger survives helper failures.
The extra attached clients are real piped control-mode processes, not model
records; missing/failed attachment is a failure, not a skipped count assertion.

All normal success/error paths after acquisition reach one outer cleanup phase
before assertions. It attempts every registered client/process and session even
after an earlier cleanup error. The guard remains alive throughout target
absence checks, then requires a successful kill receipt and termination of its
creation-time PID. A failed creation/PID lookup, unavailable inventory, failed
kill or still-live child is an explicit failure/uncertain-cleanup result. No
`has-session` failure is accepted as a successful cleanup proof. The external
coordinator's private server/job receipt is still required for crashes or unknown
provider outcomes that prevent the in-process cleanup phase from completing.

Missing prerequisites produce explicit BLOCKED/pending, never a feature PASS.
Retain actual runner case counts, HTTP results, executable hashes, and cleanup
receipts. A guarded external deadline must bound the whole native scenario.
Sockets have finite per-operation timeouts and startup/capture polling is finite.

## Implementation limits

The existing browser JSON API is preserved deliberately as interoperability.
HTTP/auth origin checks are shared with the login-only server through
app.llm_dashboard.http_auth_boundary; this scenario exercises the main dashboard.
Checked owner operations use structured argv through Sosix, 10-second process
limits and 1MiB per-stream capture budgets. The text capture ABI has no explicit
truncation bit: output at/above the ceiling or containing its truncation marker
is refused conservatively, including exact-ceiling output. No partial snapshot
is returned as complete. Process errors are 502; unavailable tmux is 503.
Legacy unchecked std.tmux signatures remain compatibility-only. This repair
does not mount WebSocket terminal routes, select smux, or qualify all IDE/apps.

## Parser evidence and encoding invariant

The primary [tmux argv parser](https://github.com/tmux/tmux/blob/master/cmd-parse.y)
(`cmd_parse_from_arguments`) treats a final semicolon as a command boundary,
unless immediately preceded by a backslash; in that case it removes that one
backslash. The checked owner therefore inserts exactly one backslash before a
final semicolon in each logical argument. Existing backslashes, nonterminal
semicolons and arguments without a final semicolon stay byte-identical after
tmux parsing. This single-command API does not expose command-list separators.
The [official format table](https://github.com/tmux/tmux/blob/master/tmux.1)
defines `session_attached` as a client count; the checked parser accepts any
nonnegative count and maps positive values to the existing boolean field.
These source findings establish the repair rationale, not runtime qualification.
