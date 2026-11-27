# Retained private credential V2

Status: **AUTHORED_NOT_RUN**. This is an authored manual, not generated or
executed evidence. No build, test, native execution, fault injection or docgen
was run. The additional native export remains subject to policy admission.

Executable source: `test/03_system/tools/retained_private_credential_v2_spec.spl`.

The generic `io.retained_private_credential_v2` facade selects its owner by build
target. Linux and other non-Windows targets forward unchanged V1 operations.
Windows retains a protected writer root, a separately retained ReadV2 root
proved to be the same actual native directory, the original credential reader,
and every created or adopted ready-file capability. A process-local bounded
registry under an existing integer mutex gate gives copied values one phase
and generation. Peer input does not choose a platform or owner.

Both root capabilities are verified by the existing native same-directory
operation, comparing current native generations, ACLs, retained ancestry,
FILE_ID_INFO and volume-GUID identity. Path spelling is only acquisition input.
The initial file remains open without write/delete sharing and its exact bounded
bytes are rechecked before and after ready publication. Ready publication uses
a sealed private stage, native NO_REPLACE rename, then exact published-stage
identity adoption into a retained reader. No secret is logged or placed in an
evidence receipt.

The stage-retirement port has explicit outcomes: discarded and released;
published target preserved and handle released; retained failure; rejected
authority; or stale generation. Original stage name and file identity are
recorded at actual native acquisition. Disposition applies only to an exact
original binding. A native publication fact is recorded at rename success,
before fallible verification, so retirement of an already-published generation
closes only its handles and never deletes its ready target. Failed disposition,
close and temporary-resource release retain cleanup ownership.
Failed admission before any file acquisition has a separate
`no-stage-acquired` outcome: it collects only the retained native security
temporaries and never claims namespace deletion. Its native fault-injection
coverage remains NOT_RUN.
An exact native-stale retirement result retains the typed stale stage as an
explicit quarantine with no positive consumption receipt. Repeated credential
close attempts cannot forget that slot and fabricate successful cleanup; this
case requires reconciliation rather than an automatic completion claim.

Credential cleanup completion means its owned capabilities were released.
It does not mean a ready artifact was removed or an earlier uncertain ready
operation succeeded. Mutation turns preserve a separate `publication_state`
through cleanup: `not-attempted`, `not-published`, `collision`, `uncertain` or
`published`. Retirement/readback never upgrades an uncertain original operation.
Legacy V1 reports `legacy-unreported` for this additional V2 metadata.

The pure cases check exact initial/ready framing, loopback endpoint, decimal
port/PID bounds and unchanged legacy invalid-input forwarding. Native scenarios
require an actual admitted Windows self-hosted runtime linked to these sources,
an actual loopback TCP provider and independently installed protected fixtures:

| Variable | Required fixture |
|---|---|
| `RETAINED_PRIVATE_CREDENTIAL_V2_WINDOWS_PATH` | Fresh private initial credential with no `.ready` sibling; valid 32-lowercase-hex nonce, one space, 1–128 printable nonspace ASCII token, optional LF. |
| `RETAINED_PRIVATE_CREDENTIAL_V2_WINDOWS_INVALID_READY_PATH` | Separate valid fresh initial credential used to reject malformed readiness. |
| `RETAINED_PRIVATE_CREDENTIAL_V2_WINDOWS_CONFLICT_PATH` | Separate valid initial credential with an already-existing protected `.ready` sibling. |
| `RETAINED_PRIVATE_CREDENTIAL_V2_WINDOWS_DENIED_PATH` | Existing initial credential in a protected root whose actual ACL denies read access to the test principal. |
| `RETAINED_PRIVATE_CREDENTIAL_V2_WINDOWS_STAGE_PARENT` | Existing protected directory beneath which the test creates unique private stage-fixture children using actual retained native root capabilities. |

All parent directories must have protected trusted ownership/ACLs, trusted
non-reparse retained ancestry and a native fixed-drive path admitted by the
production root owner. Missing configuration, non-Windows native cases,
insecure fixtures, missing denied files and unavailable providers fail; there
are no fake owner fixtures or unsupported-host passing skips. Run serially.
Native owner references remain captured for diagnosis when a case fails.
The assertions do not print initial or ready credential contents.

The native scenarios cover real listener-backed publication, duplicate refusal,
copied-owner phase revocation, confirmed close, malformed ready rejection,
NO_REPLACE collision with losing-stage cleanup, actual denied initial access,
wrong-root stage retirement, deletion proven by exclusive same-name creation,
stale generation refusal and preservation of a renamed ready target.

<details>
<summary>Outstanding qualification</summary>

All scenarios are unexecuted. Native provider availability, compiler/link
behavior, OS-thread scheduling stress, registry exhaustion, real failed
CloseHandle/LocalFree and rename/disposition fault injection remain pending.
An uncertain failed rename with no provable original binding remains retained;
the owner cannot invent cleanup completion. No power-loss durability or secret
memory-zeroization claim is made. The generic smux consumer/startup composition
is owned and reviewed separately; these fixtures do not qualify it.

The original frozen foundation index is preserved. The working native stage
origin/disposition/publication-fact delta, sibling header and its single new
versioned runtime export require independent review and export-policy admission
before landing. Authored source/manual existence is not a native PASS.

</details>
