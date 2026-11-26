# Signed Linux provisioning and installed startup

Status **AUTHORED_NOT_RUN**. This scenario drives the same command dispatcher
and cleanup finalizer as the executable. It then uses the production installed
Host domain to query status and close the service.

On a dedicated Linux fixture machine, provision the installed machine profiles
and a protected parent with its trusted authority policy. Run as the original
Host process under the required native profile. Set
`SIMPLE_LINUX_PROVISION_ACCEPTANCE_INPUT_DIR` to the directory containing
`binding.sdn`, `credential.sdn`, `host-config.sdn`, `engine-policy.sdn`,
`broker-policy.sdn`, `agent-helper-template.sdn`, and
`remote-build-helper-template.sdn`. The binding must pin all input bytes,
name the actual native machine and dedicated parent, and include the remote
build template digest. Its issuer and approval signatures must still be valid
against the protected parent policy. The parent must start with no service claim
for this machine. Use a dedicated store and the required cgroup and native
service topology to support clean provision, retry, and serving opens.

1. Decode the fixture binding and derive the expected anchor and digest.
2. Run `host-linux-provision` through the production dispatcher and finalize
   cleanup. Require success, a new installation, the exact anchor and digest,
   and no retained cleanup.
3. Retry the exact command. Require success, the duplicate disposition, and
   the same anchor and digest.
4. Open the actual installed anchor. Query `host-status` and require a ready
   response carrying the exact enrollment digest. Close the returned owner.
   Preserve any outstanding cleanup and fail on a refused or pending startup.

Missing fixture configuration reports a BLOCKED diagnostic and fails before
opening native resources. The scenario intentionally leaves signed records in
the fixture parent. Reprovision a fresh dedicated parent for another run.
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
    host_linux_service_enrollment_decode_v3, host_linux_service_enrollment_digest_v3}
use std.common.sdn.strict_v1.sdn_parse_strict_v1
use std.common.sdn.strict_types_v1.SdnStrictLimitsV1
use std.common.sdn.value.SdnValue
use std.nogc_sync_mut.io.env_ops.env_get
use std.nogc_sync_mut.io.file_ops.file_read_regular_no_follow_bounded
use std.nogc_sync_mut.io.host_linux_service_records_v4.host_linux_service_root_path_v4
use std.nogc_sync_mut.orchestration.host_service_domain_v2.HostServiceRequestV2
use std.nogc_sync_mut.orchestration.host_service_domain_v3.{
    HostServiceCleanupV3, HostServiceDomainOpenV3, host_service_cleanup_v3,
    host_service_domain_open_linux_service_v3, host_service_domain_close_v3, host_service_domain_turn_v3}

var provision_startup_pending_v3: Option<HostServiceCleanupV3> = None

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
    it "should publish a signed remote build template, retry exactly, and report the installed service ready":
        # @req HOST-01
        val input = env_get("SIMPLE_LINUX_PROVISION_ACCEPTANCE_INPUT_DIR")
        if input == "":
            fail("BLOCKED: dedicated Linux provision-to-startup fixture is unset")
            return
        if provision_startup_pending_v3.is_some():
            fail("prior native fixture cleanup is still pending")
            return
        step("Read the actual signed binding and require the remote build template pin")
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
        val args = ["host-linux-provision", input + "/binding.sdn", input + "/credential.sdn",
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
