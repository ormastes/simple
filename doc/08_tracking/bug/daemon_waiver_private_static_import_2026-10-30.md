# Test daemon waiver names cross a private-static boundary

Status: source repair; native validation pending. Separate from the accessor SIGSEGV.

Retained evidence: `/tmp/simple-doctest-runner16-build-20261030/build.log` reports:

    imported non-public module static 'app_test_daemon_types__TEST_DAEMON_MCDC_WAIVER_VARS' requires visibility-preserving accessor support

The frozen input `/tmp/simple-doctest-runner-target16-20261030` is unchanged.
`client.spl` imported and iterated the private array from `types.spl`. Native lowering
rejects this aggregate-static cross-module access. The public owner function
`test_daemon_mcdc_waiver_names` now reads the static locally; clients call that function.
The array remains private, its ordering and protocol remain unchanged, and the daemon
remains enabled. `NATIVE_SESSION_PROFILE_V1` in the same client's imports is already
public and does not exhibit the reported private-static condition.

The regression `test/unit/app/test_daemon/test_daemon_waiver_names_spec.spl` checks
all four names/order, actual request-to-child-env mapping, and clearing every waiver
in on mode. It does not start a daemon or spawn a child. Runtime/native tests have
not run; static guards cannot establish a successful native build or phase admission.

Open compiler limitation: visibility-preserving accessors for imported private module
statics remain unsupported. This source owner API is a scoped compatibility repair,
not an implementation of automatic compiler accessor generation. Follow-up compiler
qualification must cover private aggregate imports without exporting storage, lawful
owner access, and negative unauthorized access under the language visibility policy.
