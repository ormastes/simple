# Claude Full Team Memory Paths

> Checks team memory path validation and traversal rejection.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks team memory path validation and traversal rejection.

REQ-LLM-CARET-HIDDEN-008 applies only to team-memory enablement with derived
paths and enabled-file classification. Error construction, key sanitization,
write/key containment, and realpath mechanics remain supporting security/path
evidence.

Claim boundary: this focused owner spec proves team-memory enablement, path
derivation, containment, and fail-closed traversal behavior from
`teamMemPaths.spl`. The aggregate feature-gate registry owns the exhaustive
enablement matrix. This spec does not prove shipped CLI/TUI reachability,
host-filesystem effects, or live process behavior.

## Scenarios

### Claude full team memory paths

### supporting team-memory security and path behavior

#### create PathTraversalError with stable name

- create PathTraversalError with stable name
- Construct a traversal error
   - Expected: error.name equals `PathTraversalError`
   - Expected: error.message equals `bad path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-HIDDEN-008
# @req REQ-SSPEC-SYSTEM
step("create PathTraversalError with stable name")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Construct a traversal error")
val error = PathTraversalError.new("bad path")
expect(error.name).to_equal("PathTraversalError")
expect(error.message).to_equal("bad path")
```

</details>

#### reject dangerous path keys

- reject dangerous path keys
- Validate direct injection vectors
   - Expected: sanitizePathKey("ok/file.md").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject dangerous path keys")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Validate direct injection vectors")
expect(sanitizePathKey("ok/file.md").ok).to_equal(true)
expectPathFailure(
    sanitizePathKey("bad\u0000key"),
    "Null byte in path key: \"bad\u0000key\"",
)
expectPathFailure(
    sanitizePathKey("%2e%2e%2fsecret"),
    "URL-encoded traversal in path key: \"%2e%2e%2fsecret\"",
)
expectPathFailure(
    sanitizePathKey("．．／secret"),
    "Unicode-normalized traversal in path key: \"．．／secret\"",
)
expectPathFailure(
    sanitizePathKey("a\\b"),
    "Backslash in path key: \"a\\b\"",
)
expectPathFailure(
    sanitizePathKey("/absolute"),
    "Absolute path key: \"/absolute\"",
)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: team-memory enablement and derived paths

#### derive team memory paths below auto memory

- derive team memory paths below auto memory
- Build directory and entrypoint paths
   - Expected: isTeamMemoryEnabled(false, true) is false
   - Expected: isTeamMemoryEnabled(true, true) is true
   - Expected: getTeamMemPath("/mem/project") equals `/mem/project/team/`
   - Expected: getTeamMemEntrypoint("/mem/project") equals `/mem/project/team/MEMORY.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("derive team memory paths below auto memory")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Build directory and entrypoint paths")
expect(isTeamMemoryEnabled(false, true)).to_equal(false)
expect(isTeamMemoryEnabled(true, true)).to_equal(true)
expect(getTeamMemPath("/mem/project")).to_equal("/mem/project/team/")
expect(getTeamMemEntrypoint("/mem/project")).to_equal("/mem/project/team/MEMORY.md")
```

</details>

### supporting team-memory containment behavior

#### validate write paths with string and realpath containment

- validate write paths with string and realpath containment
- Validate safe, escaping, and symlink-escaping writes
   - Expected: safe.ok is true
   - Expected: safe.path equals `/mem/project/team/a.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validate write paths with string and realpath containment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Validate safe, escaping, and symlink-escaping writes")
val safe = validateTeamMemWritePath("/mem/project/team/a.md", "/mem/project/team/", true)
expect(safe.ok).to_equal(true)
expect(safe.path).to_equal("/mem/project/team/a.md")
expect(safe.error).to_be_nil()
expectPathFailure(
    validateTeamMemWritePath("/mem/project/team/../../secret", "/mem/project/team/", true),
    "Path escapes team memory directory: \"/mem/project/team/../../secret\"",
)
expectPathFailure(
    validateTeamMemWritePath("/mem/project/team/link", "/mem/project/team/", false),
    "Path escapes team memory directory via symlink: \"/mem/project/team/link\"",
)
expectPathFailure(
    validateTeamMemWritePath("/mem/project/team/bad\u0000name.md", "/mem/project/team/", true),
    "Null byte in path: \"/mem/project/team/bad\u0000name.md\"",
)
```

</details>

#### validate relative keys against the team directory

- validate relative keys against the team directory
- Join a relative key and reject traversal
   - Expected: safe.ok is true
   - Expected: safe.path equals `/mem/project/team/dir/a.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validate relative keys against the team directory")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Join a relative key and reject traversal")
val safe = validateTeamMemKey("dir/a.md", "/mem/project/team/", true)
expect(safe.ok).to_equal(true)
expect(safe.path).to_equal("/mem/project/team/dir/a.md")
expect(safe.error).to_be_nil()
expectPathFailure(
    validateTeamMemKey("../secret", "/mem/project/team/", true),
    "Key escapes team memory directory: \"../secret\"",
)
expectPathFailure(
    validateTeamMemKey("dir/a.md", "/mem/project/team/", false),
    "Key escapes team memory directory via symlink: \"dir/a.md\"",
)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: enabled team-memory file classification

#### classify team memory files only when enabled

- classify team memory files only when enabled
- Check enabled and disabled file detection
   - Expected: isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", true, true) is true
   - Expected: isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", false, true) is false
   - Expected: isTeamMemFile("/mem/project/team-evil/a.md", "/mem/project/team/", true, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classify team memory files only when enabled")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Check enabled and disabled file detection")
expect(isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", true, true)).to_equal(true)
expect(isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", false, true)).to_equal(false)
expect(isTeamMemFile("/mem/project/team-evil/a.md", "/mem/project/team/", true, true)).to_equal(false)
```

</details>

### supporting team-memory realpath behavior

#### fail closed for dangerous realpath states

- fail closed for dangerous realpath states
- Classify filesystem containment status
   - Expected: missing.ok is true
   - Expected: missing.path equals `ancestor`
   - Expected: teamMemPathsSourceLinesModeled() equals `292`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fail closed for dangerous realpath states")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Classify filesystem containment status")
val missing = realpathDeepestExistingStatus("ENOENT", false)
expect(missing.ok).to_equal(true)
expect(missing.path).to_equal("ancestor")
expect(missing.error).to_be_nil()
expectPathFailure(
    realpathDeepestExistingStatus("", true),
    "Dangling symlink detected (target does not exist)",
)
expectPathFailure(
    realpathDeepestExistingStatus("ELOOP", false),
    "Symlink loop detected in path",
)
expectPathFailure(
    realpathDeepestExistingStatus("EACCES", false),
    "Cannot verify path containment (EACCES)",
)
expect(teamMemPathsSourceLinesModeled()).to_equal(292)  # oracle: teamMemPathsSourceLinesModeled() must equal 292 — authoritative contract constant
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65ba938a69402d7aa06ddef6b53d42a74a382d1709416c5191b9653a1c33e10c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65ba938a69402d7aa06ddef6b53d42a74a382d1709416c5191b9653a1c33e10c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65ba938a69402d7aa06ddef6b53d42a74a382d1709416c5191b9653a1c33e10c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
