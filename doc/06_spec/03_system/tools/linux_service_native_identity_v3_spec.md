# Actual Linux service identity borrow fixture

Status: AUTHORED_NOT_RUN; source review pending. Three modern registered SOURCE cases; no binary-owned case discovery or execution is claimed. No compiler/spec/docgen/native/provisioning run. Whole service/signing/incarnation and pending-close fault qualification are NOT_COVERED.

Executable: test/03_system/tools/linux_service_native_identity_v3_spec.spl. Unchanged production identity leaf SHA-256: 3d3414d413ff749bf9810e3fcc82b3b92a751bf8e2980b0b7ccd2b0ec37a54ea.

Administrator setup (not performed) must provide the dedicated service UID, fixed root-owned machine/fresh-epoch/supervisor profiles, genuine system-manager/current main process topology, enforced parent/supervisor cgroups, protected store and probe-free cohort. Run as the actual original Host. Ordinary shell/default Podman/caller path is not equivalent. Missing provision fails before further effects; it never skips or claims setup complete. Supporting preparation→successor custody is not admission/launch/enrollment.

## Case 1 — actual contexts and closed reader refusal

Setup: require the pre-open guard; retain every actual factory/transition owner before checking status; establish original native host context and separate zero-argument reader without another writer.

Action: compare all seven borrowed identity fields to actual reader/epoch/native observations. Copy borrow, close original reader, then observe still-live successor.

Oracle: exact machine/boot/architecture/provider generation/process identity/process-context generation/namespace; no constant generation. Copied current/new borrow with closed reader refuse. Close original successor through actual owner-bearing cleanup. Next scenario is allowed only after both original closes positively complete with no diagnostic.

## Case 2 — closed successor refusal while reader stays current

Setup: a new genuine pair is allowed only after prior actual cleanup conclusively completes.

Action: save actual host/identity observations, close successor, observe separate original reader, try old/new borrow, then close reader.

Oracle: reader remains current; original provider generation matches saved actual observation; old/new borrow refuse. Returned typed cleanup owners are retained. Pending, stale/unknown or consumed-error leaves first diagnostic sticky and blocks another setup. A conclusively consumed native handle is never retried.

## Case 3 — refuse another setup with a real unresolved pair

Setup: open a genuine pair and leave both actual owners live. No synthetic pending-close result or capability is constructed.

Action: call the exact availability guard used by pair_open before all factories; save actual reader/successor current observations, then clean up original pair.

Oracle: exact service-identity-fixture-prior-pair-unresolved refusal while saved real partner observations are current; no second factory is called. Both original positive cleanup results can reopen the fixture gate. Any actual cleanup uncertainty retains real custody/first diagnostic, fails finish and blocks later acquisition.

## Remaining fault evidence and cleanup policy

Actual pending/consumed-close fault producer is unavailable: NOT_RUN/NOT_COVERED. Future real fault fixture must retain returned original typed owner, save actual first diagnostic, invoke guarded next setup without native acquisition and require that exact quarantined diagnostic. Preserve pending owner for authorized cleanup; never overwrite flags, inject fake close result/owner, reset after_each or accept arbitrary error as proof. Closed array aliases are not resource-state evidence.

Identity DATA is not enrollment, service scope/incarnation, signing authority or readiness. HOST03/04 receives supporting identity cases only. Actual fork/process/namespace/profile replacement, full signing lifecycle, binary-owned inventory, compiled execution and docgen completeness remain required unexecuted gates. This manual is authored, not generated.

<details>
<summary>Exact executable SSpec (authored, not run)</summary>

```simple
# codex-system-test
# AUTHORED_NOT_RUN. Real fixed installed caps only; no fake PID, namespace,
# generation, enrollment, journal grant or service incarnation is constructed.
# This observes supporting preparation custody, not full service readiness.
use std.spec.{describe, it, expect, step, fail}
use std.nogc_sync_mut.io.linux_machine_policy_owner_v1.*
use std.nogc_sync_mut.io.linux_installed_fresh_epoch_owner_v1.*
use std.nogc_sync_mut.io.linux_service_native_identity_v3.*

struct ServiceIdentityFixturePairV3:
    reader: LinuxMachinePolicyOwnerV1
    successor: LinuxFreshEpochSuccessorCustodyV1

var service_identity_readers_v3: [LinuxMachinePolicyOwnerV1] = []
var service_identity_preparations_v3: [LinuxInstalledFreshEpochOwnerV1] = []
var service_identity_successors_v3: [LinuxFreshEpochSuccessorCustodyV1] = []

# Fixture isolation only, never an identity/admission proof or resource registry.
# Closed aliases remain in the typed retention arrays; array length is not a
# pending-resource oracle. Only actual close results can complete a pair.
var service_identity_pair_unresolved_v3: bool = false
var service_identity_reader_closed_v3: bool = false
var service_identity_successor_closed_v3: bool = false
var service_identity_first_error_v3: text = ""

fn service_identity_quarantine_v3(reason: text):
    if service_identity_first_error_v3 == "": service_identity_first_error_v3 = reason
    service_identity_pair_unresolved_v3 = true

fn service_identity_pair_available_v3() -> Result<(), text>:
    if service_identity_first_error_v3 != "":
        return Err("service-identity-fixture-quarantined:" + service_identity_first_error_v3)
    if service_identity_pair_unresolved_v3:
        return Err("service-identity-fixture-prior-pair-unresolved")
    Ok(())

fn service_identity_reader_close_v3(owner: LinuxMachinePolicyOwnerV1) -> text:
    val closed = owner.close_v1()
    if closed == "released":
        service_identity_reader_closed_v3 = true
    else:
        # Original typed owner is already retained. A consumed-error is never
        # retried; stale/unknown is never promoted to positive release.
        service_identity_quarantine_v3("reader-close:" + closed)
    expect(closed).to_equal("released")
    closed

fn service_identity_preparation_close_v3(owner: LinuxInstalledFreshEpochOwnerV1):
    val closed = owner.close_v1()
    if closed.owner.is_some(): service_identity_preparations_v3.push(closed.owner.unwrap())
    if not closed.closed or closed.owner.is_some() or closed.error != "":
        service_identity_quarantine_v3("preparation-close:" + closed.error)
    expect(closed.closed).to_equal(true)
    expect(closed.owner.is_none()).to_equal(true)
    expect(closed.error).to_equal("")

fn service_identity_successor_close_v3(owner: LinuxFreshEpochSuccessorCustodyV1):
    val closed = owner.close_v1()
    if closed.owner.is_some(): service_identity_successors_v3.push(closed.owner.unwrap())
    if closed.closed and closed.owner.is_none() and closed.error == "":
        service_identity_successor_closed_v3 = true
    else:
        service_identity_quarantine_v3("successor-close:" + closed.error)
    expect(closed.closed).to_equal(true)
    expect(closed.owner.is_none()).to_equal(true)
    expect(closed.error).to_equal("")

fn service_identity_pair_finish_v3():
    # Never reset the first diagnostic or retry any consumed resource.
    if (service_identity_reader_closed_v3 and service_identity_successor_closed_v3
            and service_identity_first_error_v3 == ""):
        service_identity_pair_unresolved_v3 = false
    expect(service_identity_pair_available_v3().is_ok()).to_equal(true)

fn service_identity_pair_open_v3() -> Option<ServiceIdentityFixturePairV3>:
    # Gate precedes every actual factory/transition, including after a prior
    # setup error, unexpected early exit or pending owner-bearing close.
    val available = service_identity_pair_available_v3()
    if available.is_err():
        fail(available.unwrap_err())
        return nil
    service_identity_pair_unresolved_v3 = true
    service_identity_reader_closed_v3 = false
    service_identity_successor_closed_v3 = false
    val preparation = match linux_installed_fresh_epoch_open_v1():
        case LinuxFreshEpochOpenV1.Rejected(reason):
            service_identity_quarantine_v3("real installed epoch unavailable:" + reason)
            fail(service_identity_first_error_v3)
            return nil
        case LinuxFreshEpochOpenV1.CleanupRequired(owner, reason):
            service_identity_preparations_v3.push(owner)
            service_identity_quarantine_v3("real epoch setup cleanup required:" + reason)
            service_identity_preparation_close_v3(owner)
            fail(service_identity_first_error_v3)
            return nil
        case LinuxFreshEpochOpenV1.Ready(owner):
            service_identity_preparations_v3.push(owner)
            owner
    val consumed = preparation.consume_preparation_v1()
    if consumed.preparation.is_some(): service_identity_preparations_v3.push(consumed.preparation.unwrap())
    if consumed.successor.is_some(): service_identity_successors_v3.push(consumed.successor.unwrap())
    if consumed.error != "" or consumed.successor.is_none() or consumed.preparation.is_some():
        service_identity_quarantine_v3("actual supporting successor transition unavailable:" + consumed.error)
        if val owner = consumed.preparation:
            service_identity_preparation_close_v3(owner)
        if val owner = consumed.successor: service_identity_successor_close_v3(owner)
        fail("actual supporting successor transition unavailable:" + consumed.error)
        return nil
    val successor = consumed.successor.unwrap()
    # Match the real upper opener: establish the original native context in
    # its genuine owner before borrowing it; this leaf opens no native owner.
    val original_context = successor.current_host_context_v2()
    if original_context.is_err():
        service_identity_quarantine_v3("actual original native context unavailable:" + original_context.unwrap_err())
        service_identity_successor_close_v3(successor)
        fail("actual original native context unavailable:" + original_context.unwrap_err())
        return nil
    val reader = match linux_machine_policy_open_v1():
        case LinuxMachinePolicyOpenV1.Rejected(reason):
            service_identity_quarantine_v3("real separate reader unavailable:" + reason)
            service_identity_successor_close_v3(successor)
            fail("real separate reader unavailable:" + reason)
            return nil
        case LinuxMachinePolicyOpenV1.CleanupRequired(owner, reason):
            service_identity_readers_v3.push(owner)
            service_identity_quarantine_v3("real separate reader setup failed:" + reason)
            val closed = service_identity_reader_close_v3(owner)
            service_identity_successor_close_v3(successor)
            fail("real separate reader setup failed:" + reason + ":" + closed)
            return nil
        case LinuxMachinePolicyOpenV1.Ready(owner):
            service_identity_readers_v3.push(owner)
            owner
    Some(ServiceIdentityFixturePairV3(reader: reader, successor: successor))

describe "Genuine Linux native service identity observation borrow":
    it "should report actual independent contexts and reject a closed reader alias [IDENTITY-001/002]":
        step("Require real installed service/proc/manager/cgroup/store provision; missing setup fails")
        val opened = service_identity_pair_open_v3()
        if opened.is_none(): return
        val pair = opened.unwrap()
        val process = pair.reader.actual_process_context_v1()
        val boot = pair.reader.actual_boot_id_v2()
        val epoch = pair.successor.current_v1()
        val host = pair.successor.current_host_context_v2()
        val borrowed = linux_service_native_identity_borrow_v3(pair.reader, pair.successor)
        if process.is_err() or boot.is_err() or epoch.is_err() or host.is_err() or borrowed.is_err():
            val reason = if process.is_err(): process.unwrap_err() else if boot.is_err(): boot.unwrap_err() else if epoch.is_err(): epoch.unwrap_err() else if host.is_err(): host.unwrap_err() else: borrowed.unwrap_err()
            service_identity_quarantine_v3("actual live identity pair observations unavailable:" + reason)
            val closed = service_identity_reader_close_v3(pair.reader)
            service_identity_successor_close_v3(pair.successor)
            fail("actual live identity pair observations unavailable:" + closed)
            return
        val identity = borrowed.unwrap()
        val alias = identity
        val current = identity.current_v3()
        if current.is_err():
            service_identity_quarantine_v3("actual identity observation refused:" + current.unwrap_err())
            val closed = service_identity_reader_close_v3(pair.reader)
            service_identity_successor_close_v3(pair.successor)
            fail("actual identity observation refused:" + current.unwrap_err() + ":" + closed)
            return
        val value = current.unwrap()
        expect(value.native_machine_id).to_equal(host.unwrap().native_machine_id)
        expect(value.native_boot_id).to_equal(boot.unwrap())
        expect(value.architecture).to_equal(host.unwrap().architecture)
        expect(value.owner_generation).to_equal(host.unwrap().owner_generation)
        expect(value.process_generation).to_equal(process.unwrap().generation)
        expect(value.process_identity_digest).to_equal(epoch.unwrap().process_identity_digest)
        expect(value.authority_namespace_id).to_equal(process.unwrap().authority_namespace_id)
        step("Only original owners close; borrowed identity has no close or raw-cap getter")
        val closed = service_identity_reader_close_v3(pair.reader)
        expect(closed).to_equal("released")
        expect(pair.successor.current_host_context_v2().is_ok()).to_equal(true)
        expect(alias.current_v3().is_err()).to_equal(true)
        expect(linux_service_native_identity_borrow_v3(pair.reader, pair.successor).is_err()).to_equal(true)
        service_identity_successor_close_v3(pair.successor)
        service_identity_pair_finish_v3()

    it "should reject a closed successor while the actual separate reader stays current [IDENTITY-002]":
        step("Open a new genuine pair; never substitute a constant provider generation")
        val opened = service_identity_pair_open_v3()
        if opened.is_none(): return
        val pair = opened.unwrap()
        val borrowed = linux_service_native_identity_borrow_v3(pair.reader, pair.successor)
        if borrowed.is_err():
            service_identity_quarantine_v3("actual new identity borrow unavailable:" + borrowed.unwrap_err())
            val closed = service_identity_reader_close_v3(pair.reader)
            service_identity_successor_close_v3(pair.successor)
            fail("actual new identity borrow unavailable:" + borrowed.unwrap_err() + ":" + closed)
            return
        val before = pair.successor.current_host_context_v2()
        val observed = borrowed.unwrap().current_v3()
        service_identity_successor_close_v3(pair.successor)
        val reader_current = pair.reader.actual_process_context_v1()
        val rejected = borrowed.unwrap().current_v3()
        val reopened = linux_service_native_identity_borrow_v3(pair.reader, pair.successor)
        val closed = service_identity_reader_close_v3(pair.reader)
        expect(closed).to_equal("released")
        expect(reader_current.is_ok()).to_equal(true)
        expect(before.is_ok()).to_equal(true)
        expect(observed.is_ok()).to_equal(true)
        if before.is_ok() and observed.is_ok():
            expect(observed.unwrap().owner_generation).to_equal(before.unwrap().owner_generation)
        expect(rejected.is_err()).to_equal(true)
        expect(reopened.is_err()).to_equal(true)
        service_identity_pair_finish_v3()

    it "should refuse another setup while its real original pair is unresolved [IDENTITY-FIXTURE-P2-01]":
        step("Open a genuine installed pair and keep both original capabilities live")
        val opened = service_identity_pair_open_v3()
        if opened.is_none(): return
        val pair = opened.unwrap()
        step("Require the same pre-open guard to refuse before any second factory call")
        val blocked = service_identity_pair_available_v3()
        val reader_current = pair.reader.actual_process_context_v1()
        val successor_current = pair.successor.current_host_context_v2()
        step("Close the actual original pair, retaining every returned cleanup owner")
        service_identity_reader_close_v3(pair.reader)
        service_identity_successor_close_v3(pair.successor)
        service_identity_pair_finish_v3()
        expect(blocked.is_err()).to_equal(true)
        if blocked.is_err():
            expect(blocked.unwrap_err()).to_equal("service-identity-fixture-prior-pair-unresolved")
        expect(reader_current.is_ok()).to_equal(true)
        expect(successor_current.is_ok()).to_equal(true)
```

</details>
