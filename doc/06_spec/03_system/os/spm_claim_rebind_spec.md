# SPM claim and rebind specification

**Status: focused Phase 1 diagnostic PASS — 9/9 scenarios, 294 ms (2026-10-11).** The admitted bootstrap seed executed the real production-function fixtures. This is not native syscall, guest, whole-suite, or measured coverage qualification. SPipe doc generation remains pending; this manual was updated directly from the executable source.

Evidence in `build/phase-one-storage-gui-diagnostic/`: `spm-claim-cycle-one-inputs.sdn` freezes the source/producer hashes; `spm_claim_rebind_spec/cycle-one.command.sdn`, `.log`, `.exit` and `.rss.env` retain the command, results and process receipt. The seed SHA-256 is `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. Input and producer hashes matched before/after execution. The watchdog recorded exit 0, peak RSS 214,476 KiB and quiescent=1 under the 5,859,375 KiB / 180-second cap. The nine passing scenarios include retained and new checks; they are not nine reproduced bugs fixed.

Canonical source: `test/03_system/os/spm_claim_rebind_spec.spl`. Traceability: existing feature `FR-SPM-0003` and existing scenario requirement `REQ-SSPEC-SYSTEM`.

## Scope and production owners

The scenarios invoke production `spm_claim_authorized`, `spm_claim_for_task`, and the stateful `spm_port_*` operations. They install privilege mirrors through `bridge_set_mirror`; the existing helper only constructs the mirror input. Every scenario that observes mailbox state begins with `spm_port_reset`, and each authorization case installs its own claimant mirror.

| Coverage declaration | Meaning |
|---|---|
| `src/os/kernel/ipc/spm_claim.spl` — 80% | Target only; no measured branch coverage |
| `src/os/kernel/ipc/spm_port.spl` — 80% | Target only; no measured branch coverage |

This is host-fixture evidence for production policy and in-memory mailbox transitions. It does not establish cryptographic authentication of mirrors, native syscall dispatch, request/response correlation, scheduler blocking, concurrent safety, or live guest boot. The syscall-ID scenario checks only the production numeric identifier.

## Scenario manual

### 1. denies a task without the SPM claim privilege

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Reset the port and remove the claimant's privilege path.
2. Call production authorization and claim for the unprivileged task.

Expected: Authorization is false, claim returns `-1`, and the port remains unregistered (`0`).

### 2. authorizes an id.system mirror for the SPM claim path

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Install an id.system mirror and check production claim authorization.

Expected: The production privilege bridge authorizes the installed `id.system` mirror.

### 3. rebinds the boot placeholder to the real SPM task

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Reset and register the production boot placeholder.
2. Claim the placeholder through the authorized production owner.

Expected: Placeholder registration succeeds; claim returns `0` and the registered task becomes `9203`.

### 4. is idempotent for the same claimed SPM task

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Reset the port and authorize one real task.
2. Claim twice and inspect the registered task.

Expected: Both claims return `0`; the registered task remains `9204`.

### 5. rejects a second real SPM task after claim

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Reset the port and authorize two distinct real tasks.
2. Claim with the first task, then attempt replacement by the second.

Expected: The first claim returns `0`, the competing claim returns `-2`, and ownership remains `9205`.

### 6. reserves syscall id 115 for SysSpmClaim

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Read the production SysSpmClaim syscall identifier.

Expected: The production syscall identifier is `115`. This does not execute the dispatcher.

### 7. preserves registration and mailbox when an unauthorized task claims

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Register a real owner and seed its production request and response state.
2. Deny an unrelated privilege path without changing the owner or mailbox.

Expected: The unrelated privilege path is denied with `-1`; owner `9207`, response bytes, and both FIFO requests survive unchanged.

### 8. clears placeholder mailbox state before handing ownership to a real task

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Seed the boot placeholder with a queued request and stale response.
2. Rebind through production claim and verify both mailbox stores were cleared.

Expected: Claim transfers ownership to `9209`; both the old request queue and old response disappear; a new request can be queued and consumed.

### 9. preserves queued requests and response across an idempotent real-task claim

**Trace:** `FR-SPM-0003`; `REQ-SSPEC-SYSTEM`. **Evidence class:** host-fixture.

1. Claim an empty port and seed the real owner's production mailbox.
2. Claim again with the same task and inspect preserved FIFO and response state.

Expected: The repeated claim returns `0` and keeps owner `9210`; response bytes and FIFO order remain intact.

## Evidence and reproduction

No executable or docgen command was run during this edit. The coordinator owns the admitted producer choice, bounded diagnostic, and retained command/log/exit/input receipts. Native and live-system qualification remain separate even if all nine host scenarios pass.

The removed compatibility file `test/system/spm_claim_rebind_spec.spl` was byte-identical to the original canonical file before editing. Both had SHA-256 `942b492ddc570163e177d2f81e784f11166092956ff4e83d5b6a251c84f30f45`. All six original scenarios remain, with three mailbox regressions added.

<details>
<summary>Complete executable SSpec, including imports and mirror helper</summary>

```simple
# @cover src/os/kernel/ipc/spm_claim.spl 80%
# @cover src/os/kernel/ipc/spm_port.spl 80%
# Coverage percentages are targets, not measured results.
# codex-system-test
# Purpose and audience: production SPM claim policy and mailbox state for kernel maintainers.
# @req REQ-SSPEC-SYSTEM
# research: doc/01_research/domain/sspec_documentization_maintenance.md ; plan: doc/03_plan/sspec_modernization_plan.md ; architecture: doc/04_architecture/sspec_documentization_maintenance.md ; design: doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md

# SPipe: FR-SPM-0003 SPM port claim / rebind policy behavior.
# @tag: system, spm, syscall
# Evidence: host-fixture production function calls; no native syscall dispatch or guest boot proof.

use std.spec.step

use std.spec.{describe, it, expect}
use os.kernel.ipc.spm_port.{
    SPM_PORT_WELL_KNOWN_TASK_ID, spm_port_register, spm_port_registered_task,
    spm_port_reset, spm_port_send, spm_port_listen, spm_port_post_response
}
use os.kernel.ipc.spm_claim.{spm_claim_authorized, spm_claim_for_task}
use os.kernel.privilege.privilege_bridge.{PrivilegeTokenMirror, bridge_set_mirror}
use os.kernel.types.syscall_types.{syscall_id_spm_claim}

fn claim_mirror(path: text) -> PrivilegeTokenMirror:
    PrivilegeTokenMirror(
        id_path_bytes: path.bytes(),
        authority: 1u8,
        principal_bytes: "spm".bytes(),
        sig: "sig".bytes())

describe "FR-SPM-0003: SPM claim rebind":
    # @manual scenario evidence

    it "denies a task without the SPM claim privilege":
        # @req REQ-SSPEC-SYSTEM
        step("Reset the port and remove the claimant's privilege path")
        spm_port_reset()
        bridge_set_mirror(9201u64, claim_mirror(""))
        step("Call production authorization and claim for the unprivileged task")
        expect(spm_claim_authorized(9201u64)).to_equal(false)
        expect(spm_claim_for_task(9201u64)).to_equal(-1 as i64)
        expect(spm_port_registered_task()).to_equal(0u64)

    it "authorizes an id.system mirror for the SPM claim path":
        # @req REQ-SSPEC-SYSTEM
        step("Install an id.system mirror and check production claim authorization")
        bridge_set_mirror(9202u64, claim_mirror("id.system"))
        expect(spm_claim_authorized(9202u64)).to_equal(true)

    it "rebinds the boot placeholder to the real SPM task":
        # @req REQ-SSPEC-SYSTEM
        step("Reset and register the production boot placeholder")
        spm_port_reset()
        expect(spm_port_register(SPM_PORT_WELL_KNOWN_TASK_ID)).to_equal(true)
        bridge_set_mirror(9203u64, claim_mirror("id.system"))
        step("Claim the placeholder through the authorized production owner")
        expect(spm_claim_for_task(9203u64)).to_equal(0 as i64)
        expect(spm_port_registered_task()).to_equal(9203u64)

    it "is idempotent for the same claimed SPM task":
        # @req REQ-SSPEC-SYSTEM
        step("Reset the port and authorize one real task")
        spm_port_reset()
        bridge_set_mirror(9204u64, claim_mirror("id.system"))
        step("Claim twice and inspect the registered task")
        expect(spm_claim_for_task(9204u64)).to_equal(0 as i64)
        expect(spm_claim_for_task(9204u64)).to_equal(0 as i64)
        expect(spm_port_registered_task()).to_equal(9204u64)

    it "rejects a second real SPM task after claim":
        # @req REQ-SSPEC-SYSTEM
        step("Reset the port and authorize two distinct real tasks")
        spm_port_reset()
        bridge_set_mirror(9205u64, claim_mirror("id.system"))
        bridge_set_mirror(9206u64, claim_mirror("id.system"))
        step("Claim with the first task, then attempt replacement by the second")
        expect(spm_claim_for_task(9205u64)).to_equal(0 as i64)
        expect(spm_claim_for_task(9206u64)).to_equal(-2 as i64)
        expect(spm_port_registered_task()).to_equal(9205u64)

    it "reserves syscall id 115 for SysSpmClaim":
        # @req REQ-SSPEC-SYSTEM
        step("Read the production SysSpmClaim syscall identifier")
        expect(syscall_id_spm_claim()).to_equal(115u64)

    it "preserves registration and mailbox when an unauthorized task claims":
        # @req REQ-SSPEC-SYSTEM
        step("Register a real owner and seed its production request and response state")
        spm_port_reset()
        expect(spm_port_register(9207u64)).to_equal(true)
        bridge_set_mirror(9208u64, claim_mirror("id.user"))
        expect(spm_port_send("pending".bytes()).len()).to_equal(0)
        spm_port_post_response("reply".bytes())
        step("Deny an unrelated privilege path without changing the owner or mailbox")
        expect(spm_claim_authorized(9208u64)).to_equal(false)
        expect(spm_claim_for_task(9208u64)).to_equal(-1 as i64)
        expect(spm_port_registered_task()).to_equal(9207u64)
        expect(spm_port_send("next".bytes())).to_equal("reply".bytes())
        expect(spm_port_listen()).to_equal("pending".bytes())
        expect(spm_port_listen()).to_equal("next".bytes())
        expect(spm_port_listen().len()).to_equal(0)

    it "clears placeholder mailbox state before handing ownership to a real task":
        # @req REQ-SSPEC-SYSTEM
        step("Seed the boot placeholder with a queued request and stale response")
        spm_port_reset()
        expect(spm_port_register(SPM_PORT_WELL_KNOWN_TASK_ID)).to_equal(true)
        expect(spm_port_send("boot-request".bytes()).len()).to_equal(0)
        spm_port_post_response("boot-response".bytes())
        bridge_set_mirror(9209u64, claim_mirror("id.system"))
        step("Rebind through production claim and verify both mailbox stores were cleared")
        expect(spm_claim_for_task(9209u64)).to_equal(0 as i64)
        expect(spm_port_registered_task()).to_equal(9209u64)
        expect(spm_port_listen().len()).to_equal(0)
        expect(spm_port_send("real-request".bytes()).len()).to_equal(0)
        expect(spm_port_listen()).to_equal("real-request".bytes())
        expect(spm_port_listen().len()).to_equal(0)

    it "preserves queued requests and response across an idempotent real-task claim":
        # @req REQ-SSPEC-SYSTEM
        step("Claim an empty port and seed the real owner's production mailbox")
        spm_port_reset()
        bridge_set_mirror(9210u64, claim_mirror("id.system"))
        expect(spm_claim_for_task(9210u64)).to_equal(0 as i64)
        expect(spm_port_send("first".bytes()).len()).to_equal(0)
        spm_port_post_response("retained-response".bytes())
        step("Claim again with the same task and inspect preserved FIFO and response state")
        expect(spm_claim_for_task(9210u64)).to_equal(0 as i64)
        expect(spm_port_registered_task()).to_equal(9210u64)
        expect(spm_port_send("second".bytes())).to_equal("retained-response".bytes())
        expect(spm_port_listen()).to_equal("first".bytes())
        expect(spm_port_listen()).to_equal("second".bytes())
        expect(spm_port_listen().len()).to_equal(0)
```

</details>
