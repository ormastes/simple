# Signed Linux provisioning and installed startup

Status **AUTHORED_NOT_RUN**. This scenario drives the same command dispatcher
and cleanup finalizer as the executable. It then uses the production installed
Host domain to query status and close the service.

On a dedicated Linux fixture machine, provision the installed machine profiles
and a protected parent with its trusted authority policy. Run as the original
Host process under the required native profile. Configure these fixture
environment variables.

| Variable | Fixture value |
| --- | --- |
| `SIMPLE_LINUX_PROVISION_ACCEPTANCE_INPUT_DIR` | Directory containing `binding.sdn`, `host-config.sdn`, `engine-policy.sdn`, `broker-policy.sdn`, `agent-helper-template.sdn`, and `remote-build-helper-template.sdn` |
| `SIMPLE_LINUX_PROVISION_ACCEPTANCE_DISPATCH_ROOT` | Installed controller dispatch context with the binding's policy and provider pins |
| `SIMPLE_LINUX_PROVISION_ACCEPTANCE_CONTROLLER` | Controller identity matching the HostConfig and the issuer role |
| `SIMPLE_LINUX_PROVISION_ACCEPTANCE_KEY_STORE` | Protected store holding the controller and approver role keys |
| `SIMPLE_LINUX_PROVISION_ACCEPTANCE_OUTPUT_STORE` | Fresh protected Linux store for the generated credential |
| `SIMPLE_LINUX_PROVISION_ACCEPTANCE_APPROVER` | Installed approver identity authorized for this enrollment |

The canonical binding must pin all template and configuration bytes, name the
actual native machine and dedicated parent, and include the remote build
template digest. Both role keys must authorize the exact Host and budget for
`host_enroll_v1` and remain valid for the test's ten-minute credential.
The parent must start without a service claim for this machine, and the output
store must start without the fixture operation's credential leaf under the Linux store's `journal/` directory. Use a
dedicated store and the required cgroup and native service topology to support
provision, retry, and serving opens.

1. Decode the fixture binding and derive the expected anchor and digest.
   Check the five pinned fixture inputs before creating the credential.
   A missing or mismatched file fails with its filename and leaves the
   output store available for a corrected run.
2. Run `host-linux-enrollment-issue` through the production dispatcher. Check
   the receipt against the actual protected credential file and confirm no
   outstanding cleanup. Repeat the command and require refusal with the same
   leaf, then compare the original credential bytes.
3. Run `host-linux-provision` with the generated credential and finalize
   cleanup. Require a new installation with the exact anchor and digest.
4. Retry the exact command. Require the duplicate disposition with the same
   anchor and digest.
5. Open the installed anchor. Query `host-status` and require a ready response
   carrying the exact enrollment digest. Close the returned owner. Preserve
   outstanding cleanup and fail on a refused or pending startup.

Missing fixture configuration reports a BLOCKED diagnostic and fails before
opening native resources. The scenario intentionally leaves signed records in
the fixture parent and the credential in the output store. Use fresh dedicated
stores for another run.
This test covers installation and service readiness. Actual remote build
execution has separate acceptance scenarios.

<details>
<summary>Executable SSpec source</summary>

```simple
# codex-system-test
# AUTHORED_NOT_RUN. Dedicated signed fixture and actual native machine profiles required.
use std.spec.{describe, it, expect, step, fail}
use app.orchestrator.command.orchestrator_command_v1
use app.orchestrator.reply_cleanup_v2.orchestrator_reply_cleanup_v2
use std.common.contracts.orchestration.host_linux_service_enrollment_v3.{
    HostLinuxServiceEnrollmentBindingV3, host_linux_service_enrollment_decode_v3, host_linux_service_enrollment_digest_v3}
use std.common.crypto.sha256.sha256_text
use std.common.sdn.strict_v1.sdn_parse_strict_v1
use std.common.sdn.strict_types_v1.SdnStrictLimitsV1
use std.common.sdn.value.SdnValue
use std.nogc_sync_mut.io.env_ops.env_get
use std.nogc_sync_mut.io.file_ops.file_read_regular_no_follow_bounded
use std.nogc_sync_mut.io.host_linux_service_records_v4.host_linux_service_root_path_v4
use std.nogc_sync_mut.io.host_identity_store_v1.HostIdentityStoreV1
use std.nogc_sync_mut.orchestration.host_service_domain_v2.HostServiceRequestV2
use std.nogc_sync_mut.orchestration.host_service_domain_v3.{
    HostServiceCleanupV3, HostServiceDomainOpenV3, host_service_cleanup_v3,
    host_service_domain_open_linux_service_v3, host_service_domain_close_v3, host_service_domain_turn_v3}

var provision_startup_pending_v3: Option<HostServiceCleanupV3> = None
var provision_startup_issuer_pending_v3: Option<HostIdentityStoreV1> = None

fn provision_startup_verify_input_pins_v3(input: text, binding: HostLinuxServiceEnrollmentBindingV3) -> Result<(), text>:
    val fixture_pins = [("host-config.sdn", binding.config_digest),
        ("engine-policy.sdn", binding.engine_policy_digest), ("broker-policy.sdn", binding.broker_policy_digest),
        ("agent-helper-template.sdn", binding.agent_helper_template_digest),
        ("remote-build-helper-template.sdn", binding.remote_build_template_digest)]
    for pinned in fixture_pins:
        val source = file_read_regular_no_follow_bounded(input + "/" + pinned.0, 1048576)
        if source.is_err(): return Err("dedicated fixture file is unreadable:" + pinned.0)
        if sha256_text(source.unwrap()) != pinned.1:
            return Err("dedicated fixture file does not match enrollment pin:" + pinned.0)
    Ok(())

fn provision_startup_fields_v3(source: text, expected: Dict<text, SdnValue>) -> bool:
    val parsed = sdn_parse_strict_v1(source, SdnStrictLimitsV1(max_source_bytes: 16384, max_depth: 4, max_nodes: 64))
    if parsed.is_err():
        fail("invalid provisioning or status response SDN")
        return false
    match parsed.unwrap().value:
        case SdnValue.Dict(fields):
            var matches = true
            for key in expected.keys():
                if not fields.contains_key(key):
                    fail("missing response field:" + key)
                    matches = false
                else:
                    expect(fields[key]).to_equal(expected[key])
                    if fields[key] != expected[key]: matches = false
            matches
        case _:
            fail("expected a response object")
            false

fn provision_startup_issue_v3(input: text, digest: text) -> Result<text, text>:
    val dispatch = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_DISPATCH_ROOT")
    val controller = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_CONTROLLER")
    val keys = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_KEY_STORE")
    val output = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_OUTPUT_STORE")
    val approver = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_APPROVER")
    if dispatch == "" or controller == "" or keys == "" or output == "" or approver == "":
        return Err("BLOCKED: dedicated enrollment issuer fixture is unset")
    val operation = "provision_acceptance_operation"
    val args = ["host-linux-enrollment-issue", dispatch, controller, keys, output, approver,
        input + "/binding.sdn", operation, "provision_acceptance_grant", "600000"]
    val expected_leaf = sha256_text("simple-linux-enrollment-credential-v3\n" + controller + "\n" + operation) + ".profile"
    val credential_path = output + "/journal/" + expected_leaf
    val issued = orchestrator_reply_cleanup_v2(orchestrator_command_v1(args))
    provision_startup_issuer_pending_v3 = issued.host_identity_cleanup
    expect(issued.host_identity_cleanup.is_none()).to_equal(true)
    expect(issued.exit_code).to_equal(0)
    if issued.exit_code != 0 or issued.host_identity_cleanup.is_some():
        return Err("enrollment credential issuance or cleanup failed")
    val original = file_read_regular_no_follow_bounded(credential_path, 65536)
    if original.is_err(): return Err("issued protected enrollment credential is unreadable")
    val credential = original.unwrap()
    val expected: Dict<text, SdnValue> = {"status": SdnValue.String("enrollment-credential-published"),
        "credentialLeaf": SdnValue.String(expected_leaf), "bindingDigest": SdnValue.String(digest),
        "credentialDigest": SdnValue.String(sha256_text(credential)), "fileSynced": SdnValue.Bool(true),
        "namespaceSynced": SdnValue.Bool(true), "cleanupPending": SdnValue.Bool(false)}
    if not provision_startup_fields_v3(issued.output, expected): return Err("issuer receipt did not match protected bytes")
    step("Retry controller issuance and require the existing credential to remain byte-identical")
    val repeated = orchestrator_reply_cleanup_v2(orchestrator_command_v1(args))
    provision_startup_issuer_pending_v3 = repeated.host_identity_cleanup
    expect(repeated.exit_code).to_equal(1)
    expect(repeated.host_identity_cleanup.is_none()).to_equal(true)
    if repeated.exit_code != 1 or repeated.host_identity_cleanup.is_some():
        return Err("repeat issuance did not refuse with clean custody")
    val duplicate: Dict<text, SdnValue> = {"status": SdnValue.String("existing-enrollment-credential"),
        "credentialLeaf": SdnValue.String(expected_leaf), "cleanupPending": SdnValue.Bool(false)}
    if not provision_startup_fields_v3(repeated.output, duplicate): return Err("repeat issuance changed its outcome")
    val current = file_read_regular_no_follow_bounded(credential_path, 65536)
    if current.is_err() or current.unwrap() != credential:
        return Err("repeat issuance changed or lost the original credential")
    Ok(credential_path)

fn provision_startup_command_v3(args: [text], anchor: text, digest: text, duplicate: bool) -> bool:
    val reply = orchestrator_reply_cleanup_v2(orchestrator_command_v1(args))
    provision_startup_pending_v3 = reply.service_cleanup
    expect(reply.service_cleanup.is_none()).to_equal(true)
    expect(reply.exit_code).to_equal(0)
    val expected: Dict<text, SdnValue> = {"kind": SdnValue.String("host-linux-provision-result"),
        "version": SdnValue.Int(3), "installed": SdnValue.Bool(true), "duplicate": SdnValue.Bool(duplicate),
        "cleanupPending": SdnValue.Bool(false), "anchor": SdnValue.String(anchor),
        "bindingDigest": SdnValue.String(digest), "error": SdnValue.String("")}
    val fields_match = provision_startup_fields_v3(reply.output, expected)
    reply.service_cleanup.is_none() and reply.exit_code == 0 and fields_match

fn provision_startup_open_v3(anchor: text, digest: text):
    match host_service_domain_open_linux_service_v3(anchor):
        case HostServiceDomainOpenV3.Ready(owner):
            val turn = host_service_domain_turn_v3(owner, HostServiceRequestV2("host-status", "", ""))
            val closed = host_service_domain_close_v3(turn.owner)
            provision_startup_pending_v3 = closed.cleanup
            expect(turn.exit_code).to_equal(0)
            val expected: Dict<text, SdnValue> = {"kind": SdnValue.String("linux-host-service-status"),
                "version": SdnValue.Int(4), "enrollmentDigest": SdnValue.String(digest), "state": SdnValue.String("ready")}
            expect(provision_startup_fields_v3(turn.response, expected)).to_equal(true)
            expect(closed.cleanup.is_none()).to_equal(true)
            expect(closed.closed).to_equal(true)
            expect(closed.error).to_equal("")
        case HostServiceDomainOpenV3.Pending(owner, error):
            val closed = host_service_domain_close_v3(owner)
            provision_startup_pending_v3 = closed.cleanup
            fail("installed service startup remained pending:" + error + ":close:" + closed.error)
        case HostServiceDomainOpenV3.CleanupRequired(cleanup, error):
            val closed = host_service_cleanup_v3(cleanup)
            provision_startup_pending_v3 = closed.cleanup
            fail("installed service startup refused:" + error + ":close:" + closed.error)
        case HostServiceDomainOpenV3.Rejected(error):
            fail("installed service startup rejected:" + error)

describe "Signed Linux provisioning through installed Host startup":
    it "should issue a signed credential, provision the remote template, retry exactly, and report ready":
        # @req HOST-01
        val input = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_INPUT_DIR")
        if input == "":
            fail("BLOCKED: dedicated Linux provision-to-startup fixture is unset")
            return
        if provision_startup_pending_v3.is_some() or provision_startup_issuer_pending_v3.is_some():
            fail("prior native fixture cleanup is still pending")
            return
        step("Read the canonical binding and require the remote build template pin")
        val binding_bytes = file_read_regular_no_follow_bounded(input + "/binding.sdn", 16384)
        if binding_bytes.is_err():
            fail("dedicated fixture binding file is unavailable")
            return
        val binding = host_linux_service_enrollment_decode_v3(binding_bytes.unwrap())
        if binding.is_err() or binding.unwrap().remote_build_template_digest == "":
            fail("dedicated fixture requires a canonical binding with a signed remote build template pin")
            return
        val anchor = host_linux_service_root_path_v4(binding.unwrap()).unwrap()
        val digest = host_linux_service_enrollment_digest_v3(binding.unwrap()).unwrap()
        step("Check every fixture input pin before issuing a one-use credential")
        val pins = provision_startup_verify_input_pins_v3(input, binding.unwrap())
        if pins.is_err():
            fail(pins.unwrap_err())
            return
        step("Issue an enrollment credential through the production controller and protected output store")
        val issued = provision_startup_issue_v3(input, digest)
        if issued.is_err():
            fail(issued.unwrap_err())
            return
        val args = ["host-linux-provision", input + "/binding.sdn", issued.unwrap(),
            input + "/host-config.sdn", input + "/engine-policy.sdn", input + "/broker-policy.sdn",
            input + "/agent-helper-template.sdn", input + "/remote-build-helper-template.sdn"]
        step("Provision the protected fixture through the normal orchestrator command and finalize cleanup")
        if not provision_startup_command_v3(args, anchor, digest, false): return
        step("Retry the same signed command and require the existing installation disposition")
        if not provision_startup_command_v3(args, anchor, digest, true): return
        step("Open the installed anchor, observe matching ready status, and close the original owner")
        provision_startup_open_v3(anchor, digest)
```

</details>
