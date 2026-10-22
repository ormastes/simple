# Simple Container cross-host parallel work

Status: parallel research, design, and foundation implementation drafted; native platform qualification pending. Merge owner: Codex root. Astra completed a static foundation review; final acceptance still requires executable evidence. The user's 2026-09-27 correction selects native macOS program execution on macOS and SimpleOS task execution on SimpleOS. The earlier VM route is superseded.

## Shared interface, fixed before parallel edits

- `RuntimeIdentityV1` and `RuntimeOperationV1` in `src/lib/common/contracts/container/runtime_v1.spl` remain the lifecycle envelope.
- New pure `ContainerHostCapabilityV1` and `ContainerHostRequirementV1` belong in `src/lib/common/contracts/container/host_capability_v1.spl`. Fields: `host_os`, `guest_os`, `provider_id`, `isolation_class`, `client_privilege`, `admin_setup`, `launch_capable`, `reason`; request fields: `host_os`, `guest_os`, `isolation_class`, `require_unprivileged_client`. Admission helper: `container_host_admission_reason_v1` returns an empty string only for a supported exact match.
- `client_privilege` values: `user`, `delegated`, `unavailable`. `isolation_class` values: `native-container`, `native-sandbox`; `virtual-machine` is explicitly rejected for Simple Container. A delegated provider is launch-capable only after its separately owned broker proves scoped authorization. Discovery alone cannot set that bit.
- SDN capability receipt header: `container_host_capability |field, value|`; first row `schema, simple-container-host-capability-v1`. Values are bounded, escaped text. Build-host receipts use a distinct schema with the same SDN table grammar. No JSON/YAML configuration authority.
- Test helpers: `setup_host_capability_fixture_v1`, `check_host_capability_receipt_v1`. Manual steps: `step("inspect host capability")`, `step("create isolated workload")`, `step("observe exit and destroy")`. Missing live provider paths must fail explicitly with `fail("host capability unavailable")` or an equivalent blocked result.

## File ownership

| Lane | Exclusive files | Output |
|---|---|---|
| Research | `doc/01_research/local/simple_container_cross_host_2026-09-26.md`, `doc/01_research/domain/simple_container_cross_host_2026-09-26.md`, requirement option files | Official platform facts, local code map, short options with pros/cons/effort. |
| Design | `doc/04_architecture/simple_container_cross_host.md`, `doc/05_design/simple_container_cross_host.md`, `doc/03_plan/sys_test/simple_container_cross_host.md` | Shared ownership, SDN wire, rootless policy and fail-closed backend routing. |
| Core implementation | `src/lib/common/contracts/container/host_capability_v1.spl`, matching unit spec | Pure capability admission and exact host/guest matching. |
| SDN implementation | `scripts/check/check-dist-build-host-handoff.shs`, `src/lib/common/contracts/container/host_capability_sdn_v1.spl`, matching unit spec | Machine-readable SDN output and bounded parser/formatter; preserve current script human output. |
| Platform follow-ups | New platform-specific leaves and tests; privilege policy remains to select | Linux rootless, Windows process-isolated HCS, FreeBSD jail/Podman, macOS native App Sandbox. Do not edit the dirty Linux OCI provider or other-agent hook/workflow files. |

The product API is Simple Container on every host. Podman is the current
default **engine inside the Linux OCI leaf** and an interim compatibility
backend. The platform follow-up must add an in-tree Simple Linux leaf, qualify
it against the Podman path and adversarial lifecycle cases, then switch the
Linux provider default. Windows HCS, FreeBSD jail, macOS App Sandbox, and
SimpleOS kernel leaves keep their own native execution mechanisms. This
default switch is not part of the current probe-only foundation.
All new provider policy and lifecycle implementation is in Simple `.spl`.
The macOS lane may reuse pure common values and SimpleOS ownership rules, but
must not import SimpleOS kernel/scheduler code into a hosted provider. A
Windows sibling consumes the same contracts while retaining HCS authority in
its own leaf. No C provider implementation is authorized for this lane.

Canonical mutable lifecycle state stays with each platform provider or SimpleOS `ContainerRuntime`; the common layer carries copied/frozen values and validates child observations before owner commit. No raw pointers or unbounded transport cross the provider boundary. No platform may claim a live PASS from a pure capability fixture.

## Parallel handoff, 2026-09-26

- Research and option drafts: `doc/01_research/{local,domain}/simple_container_cross_host_2026-09-26.md` and `doc/02_requirements/{feature,nfr}/simple_container_cross_host_options.md`. The user has not selected the privilege or evidence option; no final requirement is inferred.
- Architecture, detail design, and system test plan: `doc/04_architecture/simple_container_cross_host.md`, `doc/05_design/simple_container_cross_host.md`, and `doc/03_plan/sys_test/simple_container_cross_host.md`.
- Foundation source: `src/lib/common/contracts/container/host_capability_v1.spl`, `host_capability_sdn_v1.spl`, `src/lib/nogc_async_mut/container/providers/linux/host_capability_v1.spl`, and their focused unit specs. The Linux leaf reports only a live rootless Podman probe; discovery is not a completed workload.
- SDN host handoff: `scripts/check/check-dist-build-host-handoff.shs --sdn` with a distinct schema. The reviewer found noncanonical percent escaping; the SDN lane replaced it with canonical backslash escaping and added a standard-parser assertion. Shell syntax, focused SDN shell test, and whitespace checks passed after that change.
- Astra's review found no remaining P1 issue in this foundation. Simple executable tests and live macOS verification remain blocked by the previously observed test-runner exit 139 and unavailable qualified fixture; static review and shell checks are not substitutes. Windows Server and FreeBSD provider implementation awaits the privilege choice and target-host qualification.
- The prior handoff PR has not been published: the GitHub write operation was rejected by automatic approval review under this session's `never` approval policy. Keep this lane separate from unrelated dirty files and do not report it as merged.
