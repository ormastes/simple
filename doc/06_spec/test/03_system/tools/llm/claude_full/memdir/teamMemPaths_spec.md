# Claude Full Team Memory Paths

> Checks team memory path validation and traversal rejection.

<!-- sdn-diagram:id=teamMemPaths_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=teamMemPaths_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

teamMemPaths_spec -> std
teamMemPaths_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=teamMemPaths_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Team Memory Paths

Checks team memory path validation and traversal rejection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks team memory path validation and traversal rejection.

## Scenarios

### Claude full team memory paths

#### should create PathTraversalError with stable name

- Construct a traversal error
   - Expected: error.name equals `PathTraversalError`
   - Expected: error.message equals `bad path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct a traversal error")
val error = PathTraversalError.new("bad path")
expect(error.name).to_equal("PathTraversalError")
expect(error.message).to_equal("bad path")
```

</details>

#### should reject dangerous path keys

- Validate direct injection vectors
   - Expected: sanitizePathKey("ok/file.md").ok is true
   - Expected: sanitizePathKey("bad\u0000key").ok is false
   - Expected: sanitizePathKey("%2e%2e%2fsecret").ok is false
   - Expected: sanitizePathKey("．．／secret").ok is false
   - Expected: sanitizePathKey("a\\b").ok is false
   - Expected: sanitizePathKey("/absolute").ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate direct injection vectors")
expect(sanitizePathKey("ok/file.md").ok).to_equal(true)
expect(sanitizePathKey("bad\u0000key").ok).to_equal(false)
expect(sanitizePathKey("%2e%2e%2fsecret").ok).to_equal(false)
expect(sanitizePathKey("．．／secret").ok).to_equal(false)
expect(sanitizePathKey("a\\b").ok).to_equal(false)
expect(sanitizePathKey("/absolute").ok).to_equal(false)
```

</details>

#### should derive team memory paths below auto memory

- Build directory and entrypoint paths
   - Expected: isTeamMemoryEnabled(false, true) is false
   - Expected: isTeamMemoryEnabled(true, true) is true
   - Expected: getTeamMemPath("/mem/project") equals `/mem/project/team/`
   - Expected: getTeamMemEntrypoint("/mem/project") equals `/mem/project/team/MEMORY.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build directory and entrypoint paths")
expect(isTeamMemoryEnabled(false, true)).to_equal(false)
expect(isTeamMemoryEnabled(true, true)).to_equal(true)
expect(getTeamMemPath("/mem/project")).to_equal("/mem/project/team/")
expect(getTeamMemEntrypoint("/mem/project")).to_equal("/mem/project/team/MEMORY.md")
```

</details>

#### should validate write paths with string and realpath containment

- Validate safe, escaping, and symlink-escaping writes
   - Expected: safe.ok is true
   - Expected: safe.path equals `/mem/project/team/a.md`
   - Expected: validateTeamMemWritePath("/mem/project/team/../../secret", "/mem/project/team/", true).ok is false
   - Expected: validateTeamMemWritePath("/mem/project/team/link", "/mem/project/team/", false).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate safe, escaping, and symlink-escaping writes")
val safe = validateTeamMemWritePath("/mem/project/team/a.md", "/mem/project/team/", true)
expect(safe.ok).to_equal(true)
expect(safe.path).to_equal("/mem/project/team/a.md")
expect(validateTeamMemWritePath("/mem/project/team/../../secret", "/mem/project/team/", true).ok).to_equal(false)
expect(validateTeamMemWritePath("/mem/project/team/link", "/mem/project/team/", false).ok).to_equal(false)
```

</details>

#### should validate relative keys against the team directory

- Join a relative key and reject traversal
   - Expected: safe.ok is true
   - Expected: safe.path equals `/mem/project/team/dir/a.md`
   - Expected: validateTeamMemKey("../secret", "/mem/project/team/", true).ok is false
   - Expected: validateTeamMemKey("dir/a.md", "/mem/project/team/", false).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Join a relative key and reject traversal")
val safe = validateTeamMemKey("dir/a.md", "/mem/project/team/", true)
expect(safe.ok).to_equal(true)
expect(safe.path).to_equal("/mem/project/team/dir/a.md")
expect(validateTeamMemKey("../secret", "/mem/project/team/", true).ok).to_equal(false)
expect(validateTeamMemKey("dir/a.md", "/mem/project/team/", false).ok).to_equal(false)
```

</details>

#### should classify team memory files only when enabled

- Check enabled and disabled file detection
   - Expected: isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", true, true) is true
   - Expected: isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", false, true) is false
   - Expected: isTeamMemFile("/mem/project/team-evil/a.md", "/mem/project/team/", true, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check enabled and disabled file detection")
expect(isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", true, true)).to_equal(true)
expect(isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", false, true)).to_equal(false)
expect(isTeamMemFile("/mem/project/team-evil/a.md", "/mem/project/team/", true, true)).to_equal(false)
```

</details>

#### should fail closed for dangerous realpath states

- Classify filesystem containment status
   - Expected: realpathDeepestExistingStatus("ENOENT", false).ok is true
   - Expected: realpathDeepestExistingStatus("", true).ok is false
   - Expected: realpathDeepestExistingStatus("ELOOP", false).ok is false
   - Expected: realpathDeepestExistingStatus("EACCES", false).ok is false
   - Expected: teamMemPathsSourceLinesModeled() equals `292`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify filesystem containment status")
expect(realpathDeepestExistingStatus("ENOENT", false).ok).to_equal(true)
expect(realpathDeepestExistingStatus("", true).ok).to_equal(false)
expect(realpathDeepestExistingStatus("ELOOP", false).ok).to_equal(false)
expect(realpathDeepestExistingStatus("EACCES", false).ok).to_equal(false)
expect(teamMemPathsSourceLinesModeled()).to_equal(292)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
