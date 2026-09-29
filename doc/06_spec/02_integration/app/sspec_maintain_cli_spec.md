# Sspec Maintain Cli Specification

> Tests covering sspec-maintain CLI contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sspec Maintain Cli Specification

## Scenarios

### sspec-maintain CLI contract

#### shows compatibility help without requiring a path

- shows compatibility help without requiring a path
   - Expected: run_sspec_maintain(["--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows compatibility help without requiring a path")
expect(run_sspec_maintain(["--help"])).to_equal(0)
```

</details>

#### rejects an unknown operation with usage status

- rejects an unknown operation with usage status
   - Expected: run_sspec_maintain(["unknown", "fixture.spl"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an unknown operation with usage status")
expect(run_sspec_maintain(["unknown", "fixture.spl"])).to_equal(2)
```

</details>

#### reports missing input as an IO failure

- reports missing input as an IO failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports missing input as an IO failure")
expect(run_sspec_maintain([
    "scan", "build/sspec-maintain/missing_spec.spl"])).to_equal(3)
```

</details>

#### routes safe mechanical edits through EasyFix

- routes safe mechanical edits through EasyFix
   - Expected: change.changed is true
   - Expected: change.rollback_content equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes safe mechanical edits through EasyFix")
val source = "use std.spipe\ndescribe \"feature\":\n" +
    "    it \"reports the result\":\n        @step \"Run it\"\n" +
    "        expect(run_product()).to_equal(1)\n"
match preview_sspec_text_result("fixture_spec.spl", source):
    case Err(message): fail(message)
    case Ok(change):
        expect(change.changed).to_equal(true)
        expect(change.content).to_contain("use std.spec.*")
        expect(change.content).to_contain("# @step: Run it")
        expect(change.rollback_content).to_equal(source)
```

</details>

#### applies atomically only after explicit confirmation and keeps rollback

- applies atomically only after explicit confirmation and keeps rollback
   - Expected: file_atomic_write(path, source) is true
   - Expected: chmod_status equals `0`
   - Expected: stat_status equals `0`
   - Expected: mode.trim() equals `750`
   - Expected: file_read(path) ?? "" equals `changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies atomically only after explicit confirmation and keeps rollback")
val path = "/tmp/sspec_maintain_apply_spec.spl"
val rollback = "/tmp/sspec_maintain_apply.rollback"
val source = "use std.spipe\ndescribe \"feature\":\n" +
    "    it \"reports the result\":\n        @step \"Run it\"\n" +
    "        expect(run_product()).to_equal(1)\n"
expect(file_atomic_write(path, source)).to_equal(true)
val (_, _, chmod_status) = process_run("/usr/bin/chmod", ["750", path])
expect(chmod_status).to_equal(0)
expect(run_sspec_maintain(["improve", path, "--apply", "--rollback",
    rollback])).to_equal(0)
val changed = file_read(path) ?? ""
val rollback_content = file_read(rollback) ?? ""
expect(changed).to_contain("# @step: Run it")
expect(rollback_content).to_contain("before_sha256:")
expect(rollback_content).to_contain("--- original source ---")
val (mode, _, stat_status) = process_run(
    "/usr/bin/stat", ["-c", "%a", path])
expect(stat_status).to_equal(0)
expect(mode.trim()).to_equal("750")
expect(run_sspec_maintain(["improve", path, "--apply", "--rollback",
    rollback])).to_equal(0)
expect(file_read(path) ?? "").to_equal(changed)
file_delete(path)
file_delete(rollback)
```

</details>

#### scaffolds provenance structured steps and fail-fast review mappings

- scaffolds provenance structured steps and fail-fast review mappings


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("scaffolds provenance structured steps and fail-fast review mappings")
val reference = "# Feature\n## REQ-101: reports status\n" +
    "Precondition: a project exists\nAction: Run the checker\n" +
    "Expected: The status is visible in the log\nExample: green project\n"
val scaffold = scaffold_reference_text("reference.md", reference)
expect(scaffold).to_contain("Reference SHA-256:")
expect(scaffold).to_contain("# @req: REQ-101")
expect(scaffold).to_contain("step(\"Given a project exists\")")
expect(scaffold).to_contain("step(\"Run the checker\")")
expect(scaffold).to_contain("# @capture:")
expect(scaffold).to_contain("REQ-101 <- reference.md:2")
expect(scaffold).to_contain("fail(\"TODO:")
```

</details>

#### previews scaffold writes and requires apply plus overwrite confirmation

- previews scaffold writes and requires apply plus overwrite confirmation
   - Expected: file_exists(output_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("previews scaffold writes and requires apply plus overwrite confirmation")
val reference_path = "/tmp/sspec_maintain_reference.md"
val output_path = "/tmp/sspec_maintain_scaffold_spec.spl"
file_delete(output_path)
expect(file_atomic_write(reference_path,
    "# Feature\n## REQ-202: reports health\nAction: Probe health\nExpected: Health is visible\n")).to_equal(true)
expect(run_sspec_maintain(["scaffold", reference_path,
    "--output", output_path])).to_equal(0)
expect(file_exists(output_path)).to_equal(false)
expect(run_sspec_maintain(["scaffold", reference_path,
    "--output", output_path, "--apply"])).to_equal(0)
expect(file_read(output_path) ?? "").to_contain("# @req: REQ-202")
expect(run_sspec_maintain(["scaffold", reference_path,
    "--output", output_path, "--apply"])).to_equal(3)
expect(run_sspec_maintain(["scaffold", reference_path,
    "--output", output_path, "--apply", "--overwrite"])).to_equal(0)
file_delete(reference_path)
file_delete(output_path)
```

</details>

#### round trips deterministic multi-format cache payloads

- round trips deterministic multi-format cache payloads
   - Expected: decoded.identity equals `identity`
   - Expected: decoded.effective_score equals `73`
   - Expected: decoded.human_report equals `human\nreport`
   - Expected: decoded.json_report equals `{"score":73}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("round trips deterministic multi-format cache payloads")
val record = SspecCacheRecord(schema_version: "sspec-maintain-cache/v1",
    identity: "identity", effective_score: 73,
    maximum_severity_rank: 2, human_report: "human\nreport",
    json_report: "{\"score\":73}", sarif_report: "{\"runs\":[]}")
match decode_sspec_cache_record(encode_sspec_cache_record(record)):
    case Err(message): fail(message)
    case Ok(decoded):
        expect(decoded.identity).to_equal("identity")
        expect(decoded.effective_score).to_equal(73)
        expect(decoded.human_report).to_equal("human\nreport")
        expect(decoded.json_report).to_equal("{\"score\":73}")
```

</details>

#### keeps scan advisory while score and severity policies fail independently

- keeps scan advisory while score and severity policies fail independently
   - Expected: file_atomic_write(path, source) is true
   - Expected: run_sspec_maintain(["scan", path, "--no-cache"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps scan advisory while score and severity policies fail independently")
val path = "/tmp/sspec_maintain_policy_spec.spl"
val source = "use std.spec.*\ndescribe \"weak\":\n" +
    "    it \"has no oracle\":\n        step(\"Run\")\n"
expect(file_atomic_write(path, source)).to_equal(true)
expect(run_sspec_maintain(["scan", path, "--no-cache"])).to_equal(0)
expect(run_sspec_maintain(["scan", path, "--no-cache",
    "--min-score", "100"])).to_equal(1)
expect(run_sspec_maintain(["scan", path, "--no-cache",
    "--deny-severity", "blocker"])).to_equal(1)
file_delete(path)
```

</details>

#### emits pure JSON and SARIF from the public command

- emits pure JSON and SARIF from the public command
   - Expected: file_atomic_write(path, source) is true
   - Expected: json_status equals `0`
   - Expected: json.trim().starts_with("{") is true
   - Expected: json_error.trim() equals ``
   - Expected: sarif_status equals `0`
   - Expected: sarif.trim().starts_with("{") is true
   - Expected: sarif_error.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits pure JSON and SARIF from the public command")
val path = "/tmp/sspec_maintain_machine_output_spec.spl"
val source = "use std.spec.*\ndescribe \"machine output\":\n" +
    "    it \"reports ready\":\n        step(\"Run\")\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(path, source)).to_equal(true)
val (json, json_error, json_status) = process_run(sspec_maintain_test_binary(), [
    "sspec-maintain", "scan", path, "--no-cache", "--format", "json"])
expect(json_status).to_equal(0)
expect(json.trim().starts_with("{")).to_equal(true)
expect(json).to_contain("\"schema_version\":\"sspec-maintain-scope/v1\"")
expect(json).to_contain("\"cache_disposition\":\"bypass\"")
expect(json.contains("SSpec documentization maintenance")).to_be(false)
expect(json_error.trim()).to_equal("")
val (sarif, sarif_error, sarif_status) = process_run(sspec_maintain_test_binary(), [
    "sspec-maintain", "scan", path, "--no-cache", "--format", "sarif"])
expect(sarif_status).to_equal(0)
expect(sarif.trim().starts_with("{")).to_equal(true)
expect(sarif).to_contain("\"version\":\"2.1.0\"")
expect(sarif).to_contain("\"runs\":[")
expect(sarif.contains("SSpec documentization maintenance")).to_be(false)
expect(sarif_error.trim()).to_equal("")
file_delete(path)
```

</details>

#### leaves source unchanged when rollback material cannot be retained

- leaves source unchanged when rollback material cannot be retained
   - Expected: file_atomic_write(path, source) is true
   - Expected: file_read(path) ?? "" equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("leaves source unchanged when rollback material cannot be retained")
val path = "/tmp/sspec_maintain_failed_apply_spec.spl"
val source = "use std.spipe\ndescribe \"failed apply\":\n" +
    "    it \"reports ready\":\n        @step \"Run\"\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(path, source)).to_equal(true)
expect(run_sspec_maintain(["improve", path, "--apply", "--rollback",
    "/proc/sspec-maintain-unwritable.rollback"])).to_equal(3)
expect(file_read(path) ?? "").to_equal(source)
file_delete(path)
```

</details>

#### scans deterministic directory scope and fails closed when it is empty

- scans deterministic directory scope and fails closed when it is empty
   - Expected: dir_create_all(scope) is true
   - Expected: file_atomic_write(scope + "/b_spec.spl", source) is true
   - Expected: file_atomic_write(scope + "/a_spec.spl", source) is true
   - Expected: file_atomic_write(scope + "/ignored.spl", source) is true
   - Expected: run_sspec_maintain(["scan", scope, "--no-cache"]) equals `0`
   - Expected: run_sspec_maintain(["scan", scope, "--no-cache"]) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("scans deterministic directory scope and fails closed when it is empty")
val scope = "/tmp/sspec_maintain_scope"
dir_remove(scope, true)
expect(dir_create_all(scope)).to_equal(true)
val source = "use std.spec.*\ndescribe \"scope\":\n" +
    "    it \"returns ready\":\n        step(\"Run\")\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(scope + "/b_spec.spl", source)).to_equal(true)
expect(file_atomic_write(scope + "/a_spec.spl", source)).to_equal(true)
expect(file_atomic_write(scope + "/ignored.spl", source)).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--no-cache"])).to_equal(0)
file_delete(scope + "/a_spec.spl")
file_delete(scope + "/b_spec.spl")
expect(run_sspec_maintain(["scan", scope, "--no-cache"])).to_equal(3)
dir_remove(scope, true)
```

</details>

#### reuses content-addressed cache and invalidates source and mirror changes

- reuses content-addressed cache and invalidates source and mirror changes
   - Expected: run_sspec_maintain(["scan", path, "--cache", cache]) equals `0`
   - Expected: run_sspec_maintain(["scan", path, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count`
   - Expected: file_atomic_write(path, (file_read(path) ?? "") + "\n# changed\n") is true
   - Expected: run_sspec_maintain(["scan", path, "--cache", cache]) equals `0`
   - Expected: file_atomic_write(mirror, "# Manual\n") is true
   - Expected: run_sspec_maintain(["scan", path, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `before_bypass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reuses content-addressed cache and invalidates source and mirror changes")
val path = "/tmp/sspec_maintain_cache_spec.spl"
val mirror = "/tmp/sspec_maintain_cache_spec.md"
val cache = "/tmp/sspec_maintain_cache_records"
dir_remove(cache, true)
file_delete(mirror)
expect(file_atomic_write(path,
    "use std.spec.*\ndescribe \"cache\":\n    it \"returns ready\":\n" +
    "        step(\"Run\")\n        expect(status()).to_equal(\"ready\")\n")).to_equal(true)
expect(run_sspec_maintain(["scan", path, "--cache", cache])).to_equal(0)
val first_count = dir_walk(cache).len()
expect(first_count).to_be_greater_than(0)
expect(run_sspec_maintain(["scan", path, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count)
expect(file_atomic_write(path, (file_read(path) ?? "") + "\n# changed\n")).to_equal(true)
expect(run_sspec_maintain(["scan", path, "--cache", cache])).to_equal(0)
val source_changed_count = dir_walk(cache).len()
expect(source_changed_count).to_be_greater_than(first_count)
expect(file_atomic_write(mirror, "# Manual\n")).to_equal(true)
expect(run_sspec_maintain(["scan", path, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_be_greater_than(source_changed_count)
val before_bypass = dir_walk(cache).len()
expect(run_sspec_maintain(["scan", path, "--cache", cache,
    "--no-cache"])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(before_bypass)
file_delete(path)
file_delete(mirror)
dir_remove(cache, true)
```

</details>

#### reuses unchanged pairs when one file in a directory changes

- reuses unchanged pairs when one file in a directory changes
   - Expected: dir_create_all(scope) is true
   - Expected: file_atomic_write(scope + "/a_spec.spl", source) is true
   - Expected: file_atomic_write(scope + "/b_spec.spl", source) is true
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: first_count equals `2`
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count`
   - Expected: file_atomic_write(scope + "/a_spec.spl", source + "# edited\n") is true
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count + 1`
   - Expected: file_atomic_write(scope + "/c_spec.spl", source) is true
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count + 2`
   - Expected: file_delete(scope + "/c_spec.spl") is true
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count + 2`
   - Expected: file_rename(scope + "/b_spec.spl", scope + "/renamed_spec.spl") is true
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count + 3`
   - Expected: run_sspec_maintain(["scan", scope, "--cache", cache]) equals `0`
   - Expected: dir_walk(cache).len() equals `first_count + 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reuses unchanged pairs when one file in a directory changes")
val scope = "/tmp/sspec_maintain_pair_cache_scope"
val cache = "/tmp/sspec_maintain_pair_cache_records"
dir_remove(scope, true)
dir_remove(cache, true)
expect(dir_create_all(scope)).to_equal(true)
val source = "use std.spec.*\ndescribe \"cache pair\":\n" +
    "    it \"returns ready\":\n        step(\"Run\")\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(scope + "/a_spec.spl", source)).to_equal(true)
expect(file_atomic_write(scope + "/b_spec.spl", source)).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
val first_count = dir_walk(cache).len()
expect(first_count).to_equal(2)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count)
expect(file_atomic_write(scope + "/a_spec.spl", source + "# edited\n")).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count + 1)
expect(file_atomic_write(scope + "/c_spec.spl", source)).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count + 2)
expect(file_delete(scope + "/c_spec.spl")).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count + 2)
expect(file_rename(scope + "/b_spec.spl", scope + "/renamed_spec.spl")).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count + 3)
expect(file_atomic_write(derive_manual_path(scope + "/a_spec.spl"),
    "# changed manual\n")).to_equal(true)
expect(run_sspec_maintain(["scan", scope, "--cache", cache])).to_equal(0)
expect(dir_walk(cache).len()).to_equal(first_count + 4)
dir_remove(scope, true)
dir_remove(cache, true)
```

</details>

#### previews and applies deterministic directory improvements with one rollback per source

- previews and applies deterministic directory improvements with one rollback per source
   - Expected: dir_create_all(scope) is true
   - Expected: file_atomic_write(scope + "/b_spec.spl", source) is true
   - Expected: file_atomic_write(scope + "/a_spec.spl", source) is true
   - Expected: run_sspec_maintain(["improve", scope]) equals `0`
   - Expected: file_read(scope + "/a_spec.spl") ?? "" equals `source`
   - Expected: run_sspec_maintain(["improve", scope, "--apply"]) equals `0`
   - Expected: file_exists(scope + "/a_spec.spl.sspec-maintain.rollback") is true
   - Expected: file_exists(scope + "/b_spec.spl.sspec-maintain.rollback") is true
   - Expected: run_sspec_maintain(["improve", scope, "--apply"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("previews and applies deterministic directory improvements with one rollback per source")
val scope = "/tmp/sspec_maintain_improve_scope"
dir_remove(scope, true)
expect(dir_create_all(scope)).to_equal(true)
val source = "use std.spipe\ndescribe \"feature\":\n" +
    "    it \"reports ready\":\n        @step \"Run\"\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(scope + "/b_spec.spl", source)).to_equal(true)
expect(file_atomic_write(scope + "/a_spec.spl", source)).to_equal(true)
expect(run_sspec_maintain(["improve", scope])).to_equal(0)
expect(file_read(scope + "/a_spec.spl") ?? "").to_equal(source)
expect(run_sspec_maintain(["improve", scope, "--apply"])).to_equal(0)
expect(file_read(scope + "/a_spec.spl") ?? "").to_contain("# @step: Run")
expect(file_read(scope + "/b_spec.spl") ?? "").to_contain("# @step: Run")
expect(file_exists(scope + "/a_spec.spl.sspec-maintain.rollback")).to_equal(true)
expect(file_exists(scope + "/b_spec.spl.sspec-maintain.rollback")).to_equal(true)
expect(run_sspec_maintain(["improve", scope, "--apply"])).to_equal(0)
dir_remove(scope, true)
```

</details>

#### keeps improve timing diagnostics on stderr

- keeps improve timing diagnostics on stderr
   - Expected: file_atomic_write(path, source) is true
   - Expected: status equals `0`
   - Expected: output does not contain `improve timings`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps improve timing diagnostics on stderr")
val path = "/tmp/sspec_maintain_improve_timing_spec.spl"
val source = "use std.spipe\ndescribe \"timing\":\n" +
    "    it \"reports ready\":\n        @step \"Run\"\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(path, source)).to_equal(true)
val (output, diagnostic, status) = process_run(sspec_maintain_test_binary(), [
    "sspec-maintain", "improve", path, "--debug-timings"])
expect(status).to_equal(0)
expect(output.contains("improve timings")).to_equal(false)
expect(diagnostic).to_contain("preview_us=")
expect(diagnostic).to_contain("conflict_stale_us=0")
expect(diagnostic).to_contain("reparse_us=0")
file_delete(path)
```

</details>

#### reports parse and mirror lookup timings separately on stderr

- reports parse and mirror lookup timings separately on stderr
   - Expected: file_atomic_write(path, source) is true
   - Expected: status equals `0`
   - Expected: output does not contain `parse_us=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports parse and mirror lookup timings separately on stderr")
val path = "/tmp/sspec_maintain_scan_timing_spec.spl"
val source = "use std.spec.*\ndescribe \"timing\":\n" +
    "    it \"reports ready\":\n        step(\"Run\")\n" +
    "        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(path, source)).to_equal(true)
val (output, diagnostic, status) = process_run(sspec_maintain_test_binary(), [
    "sspec-maintain", "scan", path, "--no-cache", "--format", "json",
    "--debug-timings"])
expect(status).to_equal(0)
expect(output.contains("parse_us=")).to_equal(false)
expect(diagnostic).to_contain("parse_us=")
expect(diagnostic).to_contain("mirror_lookup_us=")
file_delete(path)
```

</details>

#### applies reviewed non-blocker suppressions but never hides blockers

- applies reviewed non-blocker suppressions but never hides blockers
   - Expected: updated.suppressed_count equals `1`
   - Expected: updated.findings[0].suppression_owner equals `docs-owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies reviewed non-blocker suppressions but never hides blockers")
val report = analyze_sspec_text("fixture_spec.spl",
    "use std.spec.*\ndescribe \"named behavior\":\n" +
    "    it \"returns ready\":\n        step(\"Run\")\n" +
    "        expect(product_status()).to_equal(\"ready\")\n")
match parse_sspec_suppressions("SSDOC-NAR-001|docs-owner|covered externally\n"):
    case Err(message): fail(message)
    case Ok(suppressions):
        match apply_sspec_suppressions(report, suppressions):
            case Err(message): fail(message)
            case Ok(updated):
                expect(updated.suppressed_count).to_equal(1)
                expect(updated.findings[0].suppression_owner).to_equal("docs-owner")
```

</details>

#### applies reviewed CLI suppressions to the selected non-blocker rule

- applies reviewed CLI suppressions to the selected non-blocker rule
   - Expected: file_atomic_write(path, source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies reviewed CLI suppressions to the selected non-blocker rule")
val path = "/tmp/sspec_maintain_suppression_spec.spl"
val suppressions_path = "/tmp/sspec_maintain_suppressions.txt"
val source = "\"\"\"## Audience\n## Operator workflow\n# @manual: primary\n" +
    "REQ-001\ndoc/01_research/x.md\ndoc/03_plan/x.md\n" +
    "doc/04_architecture/x.md\ndoc/05_design/x.md\n\"\"\"\n" +
    "use std.spec.*\ndescribe \"behavior\":\n    it \"returns ready\":\n" +
    "        # @req: REQ-001\n        # @capture(text)\n" +
    "        step(\"Run\")\n        expect(status()).to_equal(\"ready\")\n"
expect(file_atomic_write(path, source)).to_equal(true)
expect(file_atomic_write(suppressions_path,
    "SSDOC-NAR-001|docs-owner|audience-only fixture\n")).to_equal(true)
expect(run_sspec_maintain(["scan", path, "--no-cache", "--rule",
    "SSDOC-NAR-001", "--min-score", "100"])).to_equal(1)
expect(run_sspec_maintain(["scan", path, "--no-cache", "--rule",
    "SSDOC-NAR-001", "--min-score", "100", "--suppressions",
    suppressions_path])).to_equal(0)
file_delete(path)
file_delete(suppressions_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/sspec_maintain_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sspec-maintain CLI contract.
- sspec-maintain CLI contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SSDOC-001`
- `REQ-SSDOC-005`
- `REQ-SSDOC-007`
- `REQ-SSDOC-008`
- `REQ-SSDOC-010`
- `REQ-101:`
- `REQ-101")`
- `REQ-202:`
- `REQ-202")`
- `REQ-001\n`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1049aeacdda2e8d371641d6dcc60aafbd1dda30969beda8691a8a2e59085f27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1049aeacdda2e8d371641d6dcc60aafbd1dda30969beda8691a8a2e59085f27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1049aeacdda2e8d371641d6dcc60aafbd1dda30969beda8691a8a2e59085f27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/app/sspec_maintain_cli_spec.spl
mirror: doc/06_spec/02_integration/app/sspec_maintain_cli_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/02_integration/app/sspec_maintain_cli_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/02_integration/app/sspec_maintain_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/sspec_maintain_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/sspec_maintain_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/sspec_maintain_cli_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/app/sspec_maintain_cli_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows compatibility help without requiring a path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/sspec_maintain_cli_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown operation with usage status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/sspec_maintain_cli_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing input as an IO failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
