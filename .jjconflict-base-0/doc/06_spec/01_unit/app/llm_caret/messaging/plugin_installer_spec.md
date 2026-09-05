# plugin_installer_spec

> Composite messaging plugin plans are typed, reversible, and fail closed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# plugin_installer_spec

Composite messaging plugin plans are typed, reversible, and fail closed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Composite messaging plugin plans are typed, reversible, and fail closed.

## Scenarios

### LLM Caret composite plugin installer

#### executes an owned write only after hash preflight and creates its backup

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes an owned write only after hash preflight and creates its backup
- Apply a hash-guarded plugin plan
   - Expected: file_write(path, "user settings") is true
   - Expected: result.status equals `applied`
   - Expected: result.applied equals `1`
   - Expected: file_read(backup) equals `user settings`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("executes an owned write only after hash preflight and creates its backup")
step("Apply a hash-guarded plugin plan")
val path = "/tmp/llm_caret_plugin_executor_" + getpid().to_text()
val backup = path + ".backup"
file_delete(path)
file_delete(backup)
expect(file_write(path, "user settings")).to_equal(true)
val operation = PluginFileOperation(action: "write", path: path, backup_path: backup,
    expected_hash: plugin_content_hash("user settings"), content: "user settings\nplugin fragment",
    reason: "merge_settings_preserving_user_entries")
val plan = PluginPlan(status: "ready", reason: "test", operations: [operation], records: [], checks: [])
val result = execute_plugin_plan(plan)
expect(result.status).to_equal("applied")
expect(result.applied).to_equal(1)
expect(file_read(path)).to_contain("plugin fragment")
expect(file_read(backup)).to_equal("user settings")

val capture = UntypedCapture(label: "plugin-executor-owned-write-readback", raw_value: file_read(path), source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "plugin_installer_spec/owned-write-readback")
val comparison = compare_evidence(evidence, oracle_spec("plugin_installer_spec/owned-write-readback", [
    check_exact("value", "user settings\nplugin fragment")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)

file_delete(path)
file_delete(backup)
```

</details>

#### refuses execution when a user changes a planned target

- refuses execution when a user changes a planned target
- Reject a stale plugin ownership hash
   - Expected: file_write(path, "changed by user") is true
   - Expected: result.status equals `blocked`
   - Expected: file_read(path) equals `changed by user`
   - Expected: stale_comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses execution when a user changes a planned target")
step("Reject a stale plugin ownership hash")
val path = "/tmp/llm_caret_plugin_executor_stale_" + getpid().to_text()
file_delete(path)
expect(file_write(path, "changed by user")).to_equal(true)
val operation = PluginFileOperation(action: "write", path: path, backup_path: "",
    expected_hash: plugin_content_hash("old content"), content: "plugin content", reason: "plugin_owned_file")
val plan = PluginPlan(status: "ready", reason: "test", operations: [operation], records: [], checks: [])
val result = execute_plugin_plan(plan)
expect(result.status).to_equal("blocked")
expect(result.error).to_contain("concurrent_change")
expect(file_read(path)).to_equal("changed by user")

val stale_capture = UntypedCapture(label: "plugin-executor-stale-target-preserved", raw_value: file_read(path), source_kind: "log_line")
val stale_evidence = untyped_capture_to_canonical(stale_capture, "plugin_installer_spec/stale-target-preserved")
val stale_comparison = compare_evidence(stale_evidence, oracle_spec("plugin_installer_spec/stale-target-preserved", [
    check_exact("value", "changed by user")
]))
expect(stale_comparison.status).to_equal(EvidenceStatus.passed)

file_delete(path)
```

</details>

#### decodes the versioned integration manifest into typed agent declarations

- decodes the versioned integration manifest into typed agent declarations
- Decode required runtime, agent, MCP, configuration, migration, and policy fields
   - Expected: manifest.valid() is true
   - Expected: manifest.agents.len() equals `3`
   - Expected: manifest.agents[1].name equals `codex`
   - Expected: manifest.agents[1].app_server is true
   - Expected: manifest.agents[2].settings_fragment equals `hooks/gemini/settings.fragment.json`
   - Expected: manifest.preserve_user_entries_on_uninstall is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("decodes the versioned integration manifest into typed agent declarations")
step("Decode required runtime, agent, MCP, configuration, migration, and policy fields")
val manifest = decode_integration_manifest(manifest_text())
expect(manifest.valid()).to_equal(true)
expect(manifest.agents.len()).to_equal(3)
expect(manifest.agents[1].name).to_equal("codex")
expect(manifest.agents[1].app_server).to_equal(true)
expect(manifest.agents[2].settings_fragment).to_equal("hooks/gemini/settings.fragment.json")
expect(manifest.preserve_user_entries_on_uninstall).to_equal(true)
```

</details>

#### rejects unsupported schemas and credentials embedded in hook material

- rejects unsupported schemas and credentials embedded in hook material
- Fail the typed manifest decoder closed on an unknown schema
   - Expected: unsupported.valid() is false
- Block installation before writes when plugin material looks like a transport secret
   - Expected: plan.status equals `blocked`
   - Expected: plan.reason equals `credential_material_in_plugin_file`
   - Expected: plan.operations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unsupported schemas and credentials embedded in hook material")
step("Fail the typed manifest decoder closed on an unknown schema")
val unsupported = decode_integration_manifest(manifest_text().replace("simple.integration/v1", "simple.integration/v9"))
expect(unsupported.valid()).to_equal(false)

step("Block installation before writes when plugin material looks like a transport secret")
val manifest = decode_integration_manifest(manifest_text())
val files = [PluginOwnedFile(path: "owned/hooks.json", content: "{\"api_key\":\"secret\"}", executable: false)]
val plan = plan_plugin_install(manifest, files, [""], [true], true, true)
expect(plan.status).to_equal("blocked")
expect(plan.reason).to_equal("credential_material_in_plugin_file")
expect(plan.operations.len()).to_equal(0)
```

</details>

#### builds deterministic backup, write, ownership, hash, executable, and MCP checks

- builds deterministic backup, write, ownership, hash, executable, and MCP checks
- Plan a guarded replacement of an existing plugin-owned hook
   - Expected: first.status equals `ready`
   - Expected: first.operations[0].action equals `write`
   - Expected: first.operations[0].backup_path equals `second.operations[0].backup_path`
   - Expected: first.records[0].before_hash equals `plugin_content_hash("old hook")`
   - Expected: first.records[0].after_hash equals `plugin_content_hash("new hook")`
   - Expected: first.checks[first.checks.len() - 1].name equals `mcp_tool_discovery`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds deterministic backup, write, ownership, hash, executable, and MCP checks")
step("Plan a guarded replacement of an existing plugin-owned hook")
val manifest = decode_integration_manifest(manifest_text())
val files = [PluginOwnedFile(path: "owned/claude-hook", content: "new hook", executable: true)]
val first = plan_plugin_install(manifest, files, ["old hook"], [true], true, true)
val second = plan_plugin_install(manifest, files, ["old hook"], [true], true, true)
expect(first.status).to_equal("ready")
expect(first.operations[0].action).to_equal("write")
expect(first.operations[0].backup_path).to_equal(second.operations[0].backup_path)
expect(first.records[0].before_hash).to_equal(plugin_content_hash("old hook"))
expect(first.records[0].after_hash).to_equal(plugin_content_hash("new hook"))
expect(first.checks[first.checks.len() - 1].name).to_equal("mcp_tool_discovery")
```

</details>

#### plans settings merges only when user entries and the owned fragment are preserved

- plans settings merges only when user entries and the owned fragment are preserved
- Accept a canonical merged settings document with compare-before-write ownership
   - Expected: ready.status equals `ready`
   - Expected: ready.operations[0].reason equals `merge_settings_preserving_user_entries`
   - Expected: ready.operations[0].expected_hash equals `plugin_content_hash("{user: true}")`
- Refuse a merge that would erase user-owned settings
   - Expected: plan_plugin_settings_merge(manifest, unsafe).reason equals `settings_merge_would_remove_user_entries`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("plans settings merges only when user entries and the owned fragment are preserved")
step("Accept a canonical merged settings document with compare-before-write ownership")
val manifest = decode_integration_manifest(manifest_text())
val merge = PluginSettingsMerge(path: ".gemini/settings.json",
    current_content: "{user: true}", merged_content: "{user: true, messaging: true}",
    owned_fragment: "{messaging: true}", user_entries_preserved: true, owned_fragment_present: true)
val ready = plan_plugin_settings_merge(manifest, merge)
expect(ready.status).to_equal("ready")
expect(ready.operations[0].reason).to_equal("merge_settings_preserving_user_entries")
expect(ready.operations[0].expected_hash).to_equal(plugin_content_hash("{user: true}"))

step("Refuse a merge that would erase user-owned settings")
val unsafe = PluginSettingsMerge(path: ".gemini/settings.json",
    current_content: "{user: true}", merged_content: "{messaging: true}",
    owned_fragment: "{messaging: true}", user_entries_preserved: false, owned_fragment_present: true)
expect(plan_plugin_settings_merge(manifest, unsafe).reason).to_equal("settings_merge_would_remove_user_entries")
```

</details>

#### reports drift and preserves files changed after installation

- reports drift and preserves files changed after installation
- Check exact installed hashes and MCP discovery
   - Expected: check.status equals `failed`
- Preserve user-modified content instead of restoring or deleting it
   - Expected: uninstall.status equals `ready`
   - Expected: uninstall.reason equals `user_changes_preserved`
   - Expected: uninstall.operations[0].action equals `preserve`
   - Expected: uninstall.operations[0].reason equals `current_hash_differs_from_installed_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports drift and preserves files changed after installation")
step("Check exact installed hashes and MCP discovery")
val manifest = decode_integration_manifest(manifest_text())
val files = [PluginOwnedFile(path: "owned/codex-hook", content: "installed", executable: true)]
val installed = plan_plugin_install(manifest, files, ["before"], [true], true, true)
val check = plan_plugin_check(installed.records, ["user changed"], [true], true, true)
expect(check.status).to_equal("failed")

step("Preserve user-modified content instead of restoring or deleting it")
val uninstall = plan_plugin_uninstall(installed.records, ["user changed"])
expect(uninstall.status).to_equal("ready")
expect(uninstall.reason).to_equal("user_changes_preserved")
expect(uninstall.operations[0].action).to_equal("preserve")
expect(uninstall.operations[0].reason).to_equal("current_hash_differs_from_installed_hash")
```

</details>

#### deletes plugin-created files and restores backups only under exact hash ownership

- deletes plugin-created files and restores backups only under exact hash ownership
- Delete an unchanged path created by the plugin
   - Expected: delete_plan.operations[0].action equals `delete`
- Restore the deterministic backup for an unchanged replaced path
   - Expected: restore_plan.operations[0].action equals `restore_backup`
   - Expected: restore_plan.operations[0].backup_path equals `replaced.records[0].backup_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("deletes plugin-created files and restores backups only under exact hash ownership")
step("Delete an unchanged path created by the plugin")
val manifest = decode_integration_manifest(manifest_text())
val files = [PluginOwnedFile(path: "owned/gemini.json", content: "fragment", executable: false)]
val created = plan_plugin_install(manifest, files, [""], [true], true, true)
val delete_plan = plan_plugin_uninstall(created.records, ["fragment"])
expect(delete_plan.operations[0].action).to_equal("delete")

step("Restore the deterministic backup for an unchanged replaced path")
val replaced = plan_plugin_install(manifest, files, ["user before"], [true], true, true)
val restore_plan = plan_plugin_uninstall(replaced.records, ["fragment"])
expect(restore_plan.operations[0].action).to_equal("restore_backup")
expect(restore_plan.operations[0].backup_path).to_equal(replaced.records[0].backup_path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-013`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2dfab59723c49c7d051ea7c833faa70c6cdf390233660a643c0bd637cbc73409`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2dfab59723c49c7d051ea7c833faa70c6cdf390233660a643c0bd637cbc73409`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2dfab59723c49c7d051ea7c833faa70c6cdf390233660a643c0bd637cbc73409`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/plugin_installer_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/plugin_installer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/plugin_installer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes the versioned integration manifest into typed agent declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported schemas and credentials embedded in hook material' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/plugin_installer_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds deterministic backup, write, ownership, hash, executable, and MCP checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
