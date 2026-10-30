# Dashboard configured authentication

Source: `test/03_system/app/llm_dashboard/feature/web_login_auth_spec.spl`.
This is an authored manual, not generated execution evidence. **NOT_RUN**:
1 scenario, 8 named steps, 0 executed, 0 passed, 0 failed observed.
Compilation, actual case enumeration, provider behavior and timing remain unverified.
REQ-CMUX-012 requires the dashboard application's actual authenticated mux route;
this focused lifecycle test complements the real HTTP/process scenario in
`test/03_system/app/web_dashboard/feature/tmux_api_route_spec.spl`.

## Execution prerequisites

Use the admitted Phase3 native test runner, its matching runtime and the canonical
native-test workflow. Record producer hash, runtime hashes, source commit, exact
argv, exit status, duration, peak RSS, actual discovered/executed/failed/blocked
case counts and artifact paths. A missing producer or host provider is BLOCKED,
never a feature pass. Do not substitute the Rust seed or rebuild Phase2 here.

Run this spec serially in a fresh process. Set `SIMPLE_TEST_PRIVATE_ROOT` to an
existing absolute fixture-owned private directory. The test creates a unique
private child directory and an exclusive verifier file through the production
file facade; it restores `DASH_AUTH_FILE`, revokes fixture leases and deletes
only its file and empty directory before asserting the exercise result.
The fixture uses a public test-only credential and a verifier independently
calculated by Python `hashlib.pbkdf2_hmac`, SHA256, 600000 iterations, 32 bytes:
the fixture password is `fixture-only-\uFFFD-password` (one actual U+FFFD character).
The fixture never reads or changes an operator credential file.

## Scenario and observations

1. Reject absent configuration and the historical fabricated cookie: no
   authentication with an absent file or `local` token.
2. Load a private configured verifier and reject wrong or incomplete credentials:
   wrong password, missing password and malformed UTF8 fail. `%FF` must not
   become U+FFFD and authenticate against the positive Unicode credential.
3. Authenticate the configured password and resolve its real opaque cookie:
   stored identity matches; token is 64 lowerhex characters; mixed-case Cookie
   header resolves it; cookie is HttpOnly and SameSite=Strict. The stored token
   digest is rejected when presented as a bearer cookie.
4. Reject forged, duplicate, prefixed and folded session headers.
5. Issue independent sessions and enforce the configured registry bound:
   tokens differ; third concurrent lease fails without revoking the first two.
6. Logout revokes one lease and allows a fresh replacement with a distinct token.
7. Configuration rotation revokes old leases and real monotonic expiry revokes
   the new lease: rotate TTL to one second, verify initially live, wait 1100ms,
   and verify refused. No mock clock is used.
8. Escape reflected login values and reject malformed replacement configuration.

The eight admitted authentication attempts deliberately fit the production
eight-attempt/60-second derivation budget. No test-only reset, weaker hash cost
or injected entropy exists. A provider timeout or failed positive login fails
the scenario; a closed gate is never accepted as the positive result. This
in-process scenario does not prove real HTTP origin checks, concurrent servers,
process restart revocation, entropy fault injection or constant-time machine
code. Comparison is best effort; neither a source accumulator loop nor a runtime
optimization barrier establishes a cryptographic constant-time guarantee. Only
SHA256 digests of the random256-bit tokens are retained in the registry; passwords
still use salted PBKDF2, never direct SHA256. The separately owned real HTTP
scenario covers the network boundary.
The canonical PBKDF2 owner loops in Simple and accelerates individual SHA256
operations when supported; measure native login latency and peak RSS before
operational admission. This scenario performs six derivations at600000 iterations.
Use the coordinated600-second build/180-second lifecycle-run bounds and the
5859375KiB RSS cap; retain the live HTTP fixture's30-second login-response bound.
Preserve a timeout as a failure; do not lower the work factor.

## Operator configuration and live HTTP fixture provisioning

`DASH_AUTH_FILE` must name an absolute, regular, non-symlink SDN file of at most
4096 bytes. Restrict the containing directory and file to the operator account
(on Windows use a private directory with an explicit owner-only DACL; Unix mode
0700 directory/0600 file). The verifier itself is sensitive to offline guessing.
Do not put plaintext passwords, verifiers, session cookies or environment dumps
in reports. The application never creates a default account.

Required fields: `username` (1..64 ASCII letters, digits, `.`, `_`, `-`),
`password_salt_hex` (16 random bytes as 32 lowerhex characters),
`password_hash_hex` (32-byte PBKDF2-HMAC-SHA256 verifier as 64 lowerhex characters),
`iterations` (600000..1000000). Optional `session_ttl_seconds` defaults to3600
and accepts1..86400; `max_sessions` defaults to64 and accepts1..64.
Use a unique salt for each credential. Password input is UTF8, at most1024 bytes.
Any configuration change, removal or invalid content revokes existing leases
when the next authentication/lookup refreshes it. Restart also revokes leases.
Each authentication/lookup rereads at most4KiB through the regular-file/no-follow
owner. This deliberately avoids a silent revocation cache window. N2 native
latency/RSS qualification must include this repeated file access across both
namespaces and concurrent clients; performance is not admitted by source review.

An independent provisioning recipe, run locally with Python3 in an already
private directory, follows. `DASH_AUTH_FILE` must point to a new file. This
uses standard-library cryptography, exclusive creation and hidden password
entry; it prints no credential or verifier. File mode alone does not configure
a Windows DACL, so prepare the private directory first.

```python
import getpass, hashlib, os, re
path = os.environ['DASH_AUTH_FILE']
assert os.path.isabs(path)
username = input('Operator username: ')
assert re.fullmatch(r'[A-Za-z0-9_.-]{1,64}', username)
password = getpass.getpass('Password: ').encode('utf-8')
assert password and len(password) <= 1024
assert not any(part in password for part in (b'\x00', b'\r', b'\n'))
assert getpass.getpass('Repeat password: ').encode('utf-8') == password
salt = os.urandom(16)
verifier = hashlib.pbkdf2_hmac('sha256', password, salt, 600000, 32)
content = (f'username: "{username}"\n'
           f'password_salt_hex: "{salt.hex()}"\n'
           f'password_hash_hex: "{verifier.hex()}"\n'
           'iterations: 600000\nsession_ttl_seconds: 3600\nmax_sessions: 64\n')
fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as output:
    output.write(content)
```

For the separate real HTTP fixture, its coordinator privately supplies that
same username/password as `SIMPLE_TEST_DASHBOARD_USERNAME` and
`SIMPLE_TEST_DASHBOARD_PASSWORD`, and passes `DASH_AUTH_FILE` to the actual
dashboard child. The test performs a URL-encoded POST `/login`, captures the
actual Set-Cookie, and sends Cookie plus exact Host/Origin for mutations.
Never use the public lifecycle-test credential for an operator deployment.
Do not log the inherited environment or HTTP credential-bearing requests.

Qualification remains pending: record build failure or runtime failure as such,
preserve artifacts, repair the cause, and rerun only changed cases within the
shared six-cycle ceiling. No release admission is claimed by this manual.
