# Simpleos Ai Cli Js Node Port Specification

## Scenarios

### SimpleOS AI CLI JS/Node port manifest contract

### REQ-001 REQ-002 REQ-003: built-in manifests

#### builds deterministic Codex, Claude, and Gemini smoke manifests

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codex = codex_cli_smoke_manifest()
val claude = claude_cli_smoke_manifest()
val gemini = gemini_cli_smoke_manifest()

expect(codex.app_id).to_equal("codex")
expect(claude.app_id).to_equal("claude")
expect(gemini.app_id).to_equal("gemini")
expect(codex.runtime_kind).to_equal(AI_CLI_RUNTIME_NODE_COMPATIBLE)
expect(codex.package_version).to_equal(AI_CLI_STAGED_SMOKE_PACKAGE_VERSION)
expect(codex.package_checksum).to_equal("manifest-package-smoke:codex:20260530")
expect(codex.runtime_artifact).to_equal(AI_CLI_STAGED_SMOKE_RUNTIME_ARTIFACT)
expect(codex.unsupported_features).to_contain(AI_CLI_RUNTIME_ARTIFACT_BLOCKER_ID)
expect(ai_cli_manifest_is_valid(codex)).to_equal(true)
expect(ai_cli_capability_summary(codex)).to_contain("package=simpleos-ai-cli-codex@0.1.0-smoke.20260530")
expect(ai_cli_capability_summary(claude)).to_contain("api.anthropic.com:443")
expect(ai_cli_capability_summary(gemini)).to_contain("generativelanguage.googleapis.com:443")
```

</details>

### REQ-004 NFR-001: validation is fail-closed

#### rejects missing identity, entry, and unsupported runtimes

<details>
<summary>Executable SPipe</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_entry = AiCliManifest(
    app_id: "bad",
    display_name: "Bad",
    runtime_kind: AI_CLI_RUNTIME_NODE_COMPATIBLE,
    entry_path: "",
    args: [],
    needs_terminal: true,
    file_grants: [],
    process_grants: [],
    network_grants: [],
    credential_grants: [],
    qemu_marker_fragments: [],
    unsupported_features: [],
    package_id: "pkg",
    package_version: AI_CLI_STAGED_SMOKE_PACKAGE_VERSION,
    package_checksum: "manifest-package-smoke:bad:20260530",
    runtime_artifact: AI_CLI_STAGED_SMOKE_RUNTIME_ARTIFACT
)
expect(ai_cli_manifest_validation_error(missing_entry)).to_equal("missing entry path")

val unsupported = AiCliManifest(
    app_id: "bad",
    display_name: "Bad",
    runtime_kind: "host-node-shell",
    entry_path: "/sys/apps/bad/main.js",
    args: [],
    needs_terminal: true,
    file_grants: [],
    process_grants: [],
    network_grants: [],
    credential_grants: [],
    qemu_marker_fragments: [],
    unsupported_features: [],
    package_id: "pkg",
    package_version: AI_CLI_STAGED_SMOKE_PACKAGE_VERSION,
    package_checksum: "manifest-package-smoke:bad:20260530",
    runtime_artifact: AI_CLI_STAGED_SMOKE_RUNTIME_ARTIFACT
)
expect(ai_cli_manifest_validation_error(unsupported)).to_equal("unsupported runtime kind: host-node-shell")
```

</details>

### REQ-005 NFR-005: hardening denials

#### denies undeclared file, process, network, and credential access

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = deny_all_manifest()
expect(ai_cli_allows_file(manifest, "/home/user/work/main.spl")).to_equal(false)
expect(ai_cli_allows_process(manifest, "git")).to_equal(false)
expect(ai_cli_allows_network(manifest, "api.openai.com:443")).to_equal(false)
expect(ai_cli_allows_credential(manifest, "openai-api-key")).to_equal(false)
```

</details>

#### allows only declared grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
expect(ai_cli_allows_file(manifest, "/home/user/work/main.spl")).to_equal(true)
expect(ai_cli_allows_file(manifest, "/home/user/work")).to_equal(true)
expect(ai_cli_allows_file(manifest, "/home/user/workspace/secret.txt")).to_equal(false)
expect(ai_cli_allows_process(manifest, "git")).to_equal(true)
expect(ai_cli_allows_process(manifest, "/usr/bin/git")).to_equal(true)
expect(ai_cli_allows_process(manifest, "git --version")).to_equal(false)
expect(ai_cli_allows_network(manifest, "api.openai.com:443")).to_equal(true)
expect(ai_cli_allows_network(manifest, "API.OPENAI.COM:0443")).to_equal(true)
expect(ai_cli_allows_credential(manifest, "openai-api-key")).to_equal(true)
expect(ai_cli_allows_credential(manifest, "OPENAI-API-KEY")).to_equal(true)
expect(ai_cli_allows_credential(manifest, "process.env.OPENAI_API_KEY")).to_equal(false)
expect(ai_cli_allows_network(manifest, "example.com:443")).to_equal(false)
expect(ai_cli_allows_network(manifest, "api.openai.com")).to_equal(false)
```

</details>

#### returns VFS file boundary decisions with fail-closed denial reasons

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val allowed = ai_cli_vfs_file_decision(manifest, "read", "/home/user/work/main.spl")
val escaped = ai_cli_vfs_file_decision(manifest, "read", "/home/user/workspace/secret.txt")
val relative = ai_cli_vfs_file_decision(manifest, "read", "relative.txt")

expect(allowed.layer).to_equal("vfs")
expect(allowed.allowed).to_equal(true)
expect(allowed.reason).to_equal("allowed")
expect(escaped.allowed).to_equal(false)
expect(escaped.reason).to_equal("file-grant-denied")
expect(relative.allowed).to_equal(false)
expect(relative.reason).to_equal("invalid-path")
expect(ai_cli_vfs_file_denial_reason(deny_all_manifest(), "write", "/home/user/work/main.spl")).to_equal("file-grant-denied")
```

</details>

#### returns socket network boundary decisions with fail-closed denial reasons

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val allowed = ai_cli_socket_network_decision(manifest, "connect", "API.OPENAI.COM:0443")
val denied = ai_cli_socket_network_decision(manifest, "connect", "example.com:443")
val invalid = ai_cli_socket_network_decision(manifest, "connect", "api.openai.com")

expect(allowed.layer).to_equal("socket")
expect(allowed.subject).to_equal("api.openai.com:443")
expect(allowed.allowed).to_equal(true)
expect(allowed.reason).to_equal("allowed")
expect(denied.allowed).to_equal(false)
expect(denied.reason).to_equal("network-grant-denied")
expect(invalid.allowed).to_equal(false)
expect(invalid.reason).to_equal("invalid-endpoint")
expect(ai_cli_socket_network_denial_reason(deny_all_manifest(), "connect", "api.openai.com:443")).to_equal("network-grant-denied")
```

</details>

#### returns process spawn boundary decisions with fail-closed denial reasons

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val allowed = ai_cli_process_spawn_decision(manifest, "spawn", "/usr/bin/git")
val denied = ai_cli_process_spawn_decision(manifest, "spawn", "node")
val shell_path = ai_cli_process_spawn_decision(manifest, "spawn", "/bin/sh")
val shell_escape = ai_cli_process_spawn_decision(manifest, "spawn", "git --version")
val empty = ai_cli_process_spawn_decision(manifest, "spawn", "")

expect(allowed.layer).to_equal("process")
expect(allowed.subject).to_equal("git")
expect(allowed.allowed).to_equal(true)
expect(allowed.reason).to_equal("allowed")
expect(denied.allowed).to_equal(false)
expect(denied.reason).to_equal("process-grant-denied")
expect(shell_path.allowed).to_equal(false)
expect(shell_path.reason).to_equal("process-grant-denied")
expect(shell_escape.allowed).to_equal(false)
expect(shell_escape.reason).to_equal("invalid-command")
expect(empty.allowed).to_equal(false)
expect(empty.reason).to_equal("invalid-command")
expect(ai_cli_process_spawn_denial_reason(deny_all_manifest(), "spawn", "/usr/bin/git")).to_equal("process-grant-denied")
```

</details>

#### returns credential read boundary decisions with fail-closed denial reasons

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val allowed = ai_cli_credential_read_decision(manifest, "read", "OPENAI-API-KEY")
val denied = ai_cli_credential_read_decision(manifest, "read", "anthropic-api-key")
val ambient = ai_cli_credential_read_decision(manifest, "read", "process.env.OPENAI_API_KEY")
val token = ai_cli_credential_read_decision(manifest, "read", "sk-inline-secret")

expect(allowed.layer).to_equal("credential")
expect(allowed.subject).to_equal("openai-api-key")
expect(allowed.allowed).to_equal(true)
expect(allowed.reason).to_equal("allowed")
expect(denied.allowed).to_equal(false)
expect(denied.reason).to_equal("credential-grant-denied")
expect(ambient.allowed).to_equal(false)
expect(ambient.reason).to_equal("ambient-env-denied")
expect(token.allowed).to_equal(false)
expect(token.reason).to_equal("credential-token-denied")
expect(ai_cli_credential_read_denial_reason(deny_all_manifest(), "read", "openai-api-key")).to_equal("credential-grant-denied")
```

</details>

#### builds deterministic permission flags from manifest grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val flags = ai_cli_permission_flags(manifest)
val summary = ai_cli_permission_flag_summary(manifest)

expect(flags[0]).to_equal("--experimental-permission")
expect(summary).to_contain("--allow-fs-read=/home/user/work,/home/user/.codex,/var/cache/codex,/tmp")
expect(summary).to_contain("--allow-fs-write=/home/user/work,/home/user/.codex,/var/cache/codex,/tmp")
expect(summary).to_contain("--allow-child-process=simple,git")
expect(summary).to_contain("--allow-net=api.openai.com:443")
expect(summary).to_contain("--allow-env=openai-api-key")
```

</details>

#### keeps deny-all permission flags fail-closed

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = ai_cli_permission_flags(deny_all_manifest())
expect(flags.len()).to_equal(1)
expect(flags[0]).to_equal("--experimental-permission")
```

</details>

#### maps manifest grants to Deno-style permission flags for comparison

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val flags = ai_cli_deno_permission_flags(manifest)
val summary = ai_cli_deno_permission_flag_summary(manifest)

expect(flags[0]).to_equal("--allow-read=/home/user/work,/home/user/.codex,/var/cache/codex,/tmp")
expect(summary).to_contain("--allow-write=/home/user/work,/home/user/.codex,/var/cache/codex,/tmp")
expect(summary).to_contain("--allow-net=api.openai.com:443")
expect(summary).to_contain("--allow-run=simple,git")
expect(summary).to_contain("--allow-env=openai-api-key")
expect(ai_cli_deno_permission_flags(deny_all_manifest()).len()).to_equal(0)
```

</details>

### REQ-006 NFR-003: QEMU target and marker data

#### normalizes x85 to x86 and declares guest-side marker fragments

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val markers = ai_cli_qemu_marker_fragments(manifest, "x85")
expect(ai_cli_normalize_target("x85")).to_equal("x86")
expect(markers.len()).to_equal(6)
expect(markers[0]).to_equal("[ai-cli] qemu-target=x86")
expect(markers[1]).to_equal("[ai-cli] manifest app=codex runtime=node-compatible")
expect(markers).to_contain("[ai-cli] guest-evidence-required")
expect(markers).to_contain("[ai-cli] runtime:start app=codex")
expect(markers).to_contain("[ai-cli] hardening:ok app=codex")
```

</details>

#### declares RISC-V, x86, and ARM QEMU lanes with serial evidence paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ai_cli_qemu_lanes(codex_cli_smoke_manifest())
expect(lanes.len()).to_equal(3)
expect(lanes[0].target).to_equal("riscv")
expect(lanes[0].qemu_system).to_equal("qemu-system-riscv64")
expect(lanes[1].target).to_equal("x86")
expect(lanes[1].qemu_system).to_equal("qemu-system-x86_64")
expect(lanes[2].target).to_equal("arm")
expect(lanes[2].qemu_system).to_equal("qemu-system-aarch64")
expect(ai_cli_qemu_lane_summary(lanes[1])).to_contain("serial=build/os/ai-cli-x86_64.serial.log")
```

</details>

#### accepts only guest serial output that contains every lane marker

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = ai_cli_qemu_lane(codex_cli_smoke_manifest(), "x85")
val full_serial = lane.marker_fragments.join("\n")
val partial_serial = "[ai-cli] qemu-target=x86\n[ai-cli] manifest app=codex runtime=node-compatible"

expect(ai_cli_qemu_serial_accepts_lane(lane, full_serial)).to_equal(true)
expect(ai_cli_qemu_serial_accepts_lane(lane, partial_serial)).to_equal(false)
expect(ai_cli_qemu_missing_markers(lane, partial_serial)).to_contain("[ai-cli] guest-evidence-required")
```

</details>

### REQ-007 AC-7: full Node port blocker

#### records the later full Node/V8/libuv implementation layer

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocker = ai_cli_full_node_blocker()
expect(blocker).to_contain("Node.js/V8/libuv")
expect(blocker).to_contain("later layer")
```

</details>

#### attaches the runtime artifact blocker to each QEMU lane

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = ai_cli_qemu_lane(gemini_cli_smoke_manifest(), "arm")
expect(lane.runtime_status).to_equal("blocked-runtime-artifact")
expect(lane.blocker).to_contain("Node.js/V8/libuv")
expect(lane.blocker).to_contain(AI_CLI_RUNTIME_ARTIFACT_BLOCKER_ID)
expect(lane.marker_fragments).to_contain("[ai-cli] runtime-status=blocked-runtime-artifact")
expect(lane.marker_fragments).to_contain("[ai-cli] blocker-report app=gemini id=blocked:no-full-node-v8-libuv-artifact-20260530")
```

</details>

### AC-3 AC-4: guest provisioning plan

#### builds deterministic guest paths and disk manifest names for staged CLI packages

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val lane = ai_cli_qemu_lane(manifest, "x86")
val plan = ai_cli_provisioning_plan(manifest, lane)

expect(plan.manifest_path).to_equal("/sys/apps/codex/AI_MANIFEST.SDN")
expect(plan.launcher_path).to_equal("/sys/apps/codex/launch.spl")
expect(plan.marker_payload_path).to_equal("/sys/apps/codex/qemu_markers.txt")
expect(plan.runtime_package_path).to_equal("/sys/runtime/node-compatible/x86/runtime.smf")
expect(plan.disk_manifest_filename).to_equal("CODEX.APP")
expect(plan.command_line).to_contain("/sys/apps/codex/codex.js --version")
expect(plan.required_guest_paths).to_contain("/sys/runtime/node-compatible/x86/runtime.smf")
```

</details>

#### packages the exact lane markers that guest serial output must emit

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = claude_cli_smoke_manifest()
val lane = ai_cli_qemu_lane(manifest, "riscv")
val plan = ai_cli_provisioning_plan(manifest, lane)
val payload = ai_cli_marker_payload(manifest, lane)

expect(plan.marker_payload).to_equal(payload)
expect(payload).to_contain("[ai-cli] provisioned app=claude target=riscv")
expect(payload).to_contain("[ai-cli] runtime:start app=claude")
expect(payload).to_contain("[ai-cli] runtime-status=blocked-runtime-artifact")
expect(payload).to_contain("[ai-cli] hardening:deny app=claude reason=undeclared-capability")
expect(payload).to_contain("[ai-cli] blocker-report app=claude id=blocked:no-full-node-v8-libuv-artifact-20260530")
expect(ai_cli_provisioning_plan_summary(plan)).to_contain("disk-manifest=CLAUDE.APP")
```

</details>

#### materializes staged SimpleOS runtime smoke package contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = codex_cli_smoke_manifest()
val lane = ai_cli_qemu_lane(manifest, "x86")
val package = ai_cli_runtime_smoke_package(manifest, lane)
val summary = ai_cli_runtime_smoke_package_summary(package)

expect(package.package_root).to_equal("/sys/apps/codex")
expect(package.ready).to_equal(true)
expect(package.blocker).to_equal("")
expect(package.manifest_sdn).to_contain("app_id = \"codex\"")
expect(package.manifest_sdn).to_contain("runtime_kind = \"node-compatible\"")
expect(package.manifest_sdn).to_contain("package_version = \"0.1.0-smoke.20260530\"")
expect(package.manifest_sdn).to_contain("runtime_artifact = \"simple-js-agent-smoke-stub@20260530\"")
expect(package.manifest_sdn).to_contain("permission_flags = \"--experimental-permission --allow-fs-read=/home/user/work,/home/user/.codex,/var/cache/codex,/tmp")
expect(package.entry_source).to_contain("__simple_ai_cli_smoke")
expect(package.entry_source).to_contain("app: \"codex\"")
expect(package.entry_source).to_contain("[ai-cli-js] smoke app=codex target=x86")
expect(package.launcher_source).to_contain("[ai-cli] runtime:start app=codex")
expect(package.launcher_source).to_contain("[ai-cli] permission-flags --experimental-permission")
expect(package.launcher_source).to_contain("[ai-cli] cli-smoke:start app=codex")
expect(package.launcher_source).to_contain("[ai-cli] hardening:deny app=codex reason=undeclared-capability")
expect(package.launcher_source).to_contain("[ai-cli] hardening:ok app=codex")
expect(package.runtime_stub_source).to_contain("simple-js-agent target=x86")
expect(package.runtime_stub_source).to_contain("node-compat-surface=fs,process,stdio-tty,timers,net,tls,module-resolution,webassembly")
expect(package.runtime_stub_source).to_contain("runtime-artifact=simple-js-agent-smoke-stub@20260530")
expect(package.runtime_stub_source).to_contain("blocker-report app=codex id=blocked:no-full-node-v8-libuv-artifact-20260530")
expect(package.package_index_sdn).to_contain("disk_manifest = \"CODEX.APP\"")
expect(summary).to_contain("ready=true")
```

</details>

#### rejects smoke package sources that try host or ambient runtime escapes

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ai_cli_runtime_smoke_package_hardening_error("host.shell('id')")).to_equal("host shell access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("process.env.OPENAI_API_KEY")).to_equal("ambient environment access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("require('fs')")).to_equal("module loader access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("fetch('https://example.com')")).to_equal("network access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("fs.readFile('/etc/passwd')")).to_equal("file access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("fs.promises.writeFile('/tmp/x', 'x')")).to_equal("file access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("child_process.spawn('sh')")).to_equal("child process access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("net.connect(443, 'api.openai.com')")).to_equal("network access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("tls.connect({ host: 'api.openai.com' })")).to_equal("network access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("Deno.env.get('OPENAI_API_KEY')")).to_equal("ambient environment access denied")
expect(ai_cli_runtime_smoke_package_hardening_error("credential:openai-api-key")).to_equal("ambient environment access denied")
```

</details>

<details>
<summary>Advanced: builds a full Codex Claude Gemini by RISC-V x86 ARM smoke package matrix</summary>

#### builds a full Codex Claude Gemini by RISC-V x86 ARM smoke package matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packages = ai_cli_runtime_smoke_packages()
val evidence = ai_cli_runtime_smoke_matrix_evidence()
val summary = ai_cli_runtime_smoke_matrix_summary(evidence)

expect(packages.len()).to_equal(9)
expect(evidence.package_count).to_equal(9)
expect(evidence.ready_count).to_equal(9)
expect(evidence.serial_accept_count).to_equal(9)
expect(evidence.app_ids).to_contain("codex")
expect(evidence.app_ids).to_contain("claude")
expect(evidence.app_ids).to_contain("gemini")
expect(evidence.targets).to_contain("riscv")
expect(evidence.targets).to_contain("x86")
expect(evidence.targets).to_contain("arm")
expect(evidence.status).to_equal("ai_cli_runtime_smoke_matrix_ready")
expect(summary).to_contain("packages=9")
```

</details>


</details>

#### accepts each staged package marker payload as QEMU serial evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packages = ai_cli_runtime_smoke_packages()

expect(ai_cli_runtime_smoke_package_serial_accepted(packages[0])).to_equal(true)
expect(ai_cli_runtime_smoke_package_serial_accepted(packages[4])).to_equal(true)
expect(ai_cli_runtime_smoke_package_serial_accepted(packages[8])).to_equal(true)
```

</details>

### AC-1 AC-2: Bun-informed Simple JS runtime profile

#### keeps Bun-like single-tool lessons while preserving the Simple MDSOC boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = bun_informed_simple_js_runtime_profile()
val summary = ai_cli_runtime_profile_summary(profile)

expect(profile.profile_id).to_equal("simple-js-agent-bun-informed")
expect(summary).to_contain("single-tool-runtime-plus-package-test-bundle-surfaces")
expect(summary).to_contain("Simple-MDSOC-capsule-not-Zig-JavaScriptCore-copy")
expect(summary).to_contain("node-surface=fs,process,stdio-tty,timers,net,tls,crypto,module-resolution,package-json,child-process,credentials,webassembly")
expect(summary).to_contain("unsupported=native-node-addon-abi,ambient-host-shell,undeclared-npm-install,ambient-credential-read,unbounded-child-process-spawn")
expect(ai_cli_runtime_profile_supports_manifest(profile, codex_cli_smoke_manifest())).to_equal(true)
```

</details>

### AC-5 AC-6: Simple browser WASM GUI contract

#### allows only declared browser/WASM imports and rejects host escapes

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = simple_browser_wasm_gui_contract()
val summary = ai_cli_wasm_browser_contract_summary(contract)

expect(contract.contract_id).to_equal("simple-browser-wasm-gui-contract")
expect(summary).to_contain("targets=simple-browser,host-wm,simpleos-wm,android,ios")
expect(ai_cli_wasm_import_allowed(contract, "simple_ui.present")).to_equal(true)
expect(ai_cli_wasm_import_allowed(contract, "webgpu.requestAdapter")).to_equal(true)
expect(ai_cli_wasm_import_denied(contract, "webgpu.requestDevice")).to_equal(true)
expect(ai_cli_wasm_import_denied(contract, "webgpu.queue.submit")).to_equal(true)
expect(ai_cli_wasm_import_denied(contract, "navigator.gpu")).to_equal(true)
expect(ai_cli_wasm_import_denied(contract, "fs.readFile")).to_equal(true)
expect(ai_cli_wasm_import_denied(contract, "host.shell")).to_equal(true)
expect(ai_cli_wasm_import_denied(contract, "random.unlisted")).to_equal(true)
```

</details>

#### requires init, render, and event exports before browser execution

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = simple_browser_wasm_gui_contract()

expect(ai_cli_wasm_exports_satisfy_contract(contract, ["simple_app_init", "simple_app_render", "simple_app_event"])).to_equal(true)
expect(ai_cli_wasm_exports_satisfy_contract(contract, ["simple_app_init", "simple_app_render"])).to_equal(false)
expect(contract.qemu_marker_fragments).to_contain("[wasm-gui] browser-rendered")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/system/os/simpleos_ai_cli_js_node_port_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS AI CLI JS/Node port manifest contract
- REQ-001 REQ-002 REQ-003: built-in manifests
- REQ-004 NFR-001: validation is fail-closed
- REQ-005 NFR-005: hardening denials
- REQ-006 NFR-003: QEMU target and marker data
- REQ-007 AC-7: full Node port blocker
- AC-3 AC-4: guest provisioning plan
- AC-1 AC-2: Bun-informed Simple JS runtime profile
- AC-5 AC-6: Simple browser WASM GUI contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

