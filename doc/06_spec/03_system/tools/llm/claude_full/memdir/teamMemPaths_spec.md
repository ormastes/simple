# Claude Full Team Memory Paths

> Focused team-memory owner behavior for `REQ-LLM-CARET-HIDDEN-008`.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/memdir/teamMemPaths_spec.spl` |
| Executable scenarios | 7 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | `REQ-LLM-CARET-HIDDEN-008`, scoped only to enablement with derived paths and enabled-file classification |

## Scope and Claim Boundary

This focused manual mirrors team-memory enablement, path derivation,
containment, and fail-closed traversal behavior from `teamMemPaths.spl`. The
aggregate feature-gate registry owns the exhaustive enablement matrix. This
manual does not claim shipped CLI/TUI reachability, host-filesystem effects,
live process behavior, or runtime execution.

Every expected `PathValidationResult` failure uses the spec-local
`expectPathFailure` helper. It requires `ok == false`, an empty public `path`,
a nonnil `error`, the stable `PathTraversalError` name, and the exact production
message. The empty path assertion prevents normalized or resolved path leakage.

The requirement applies only to the enablement/path-derivation and enabled-file
classification scenarios. Error construction, key sanitization, write/key
containment, and realpath mechanics remain supporting security/path evidence.

## Scenarios

### Supporting team-memory security and path behavior

#### should create PathTraversalError with stable name

- Construct a traversal error

<details>
<summary>Executable SSpec</summary>

```simple
it "should create PathTraversalError with stable name":
    step("Construct a traversal error")
    val error = PathTraversalError.new("bad path")
    expect(error.name).to_equal("PathTraversalError")
    expect(error.message).to_equal("bad path")
```

</details>

#### should reject dangerous path keys

- Validate direct injection vectors

<details>
<summary>Executable SSpec</summary>

```simple
it "should reject dangerous path keys":
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

#### should derive team memory paths below auto memory

- Build directory and entrypoint paths

<details>
<summary>Executable SSpec</summary>

```simple
it "should derive team memory paths below auto memory":
    step("Build directory and entrypoint paths")
    expect(isTeamMemoryEnabled(false, true)).to_equal(false)
    expect(isTeamMemoryEnabled(true, true)).to_equal(true)
    expect(getTeamMemPath("/mem/project")).to_equal("/mem/project/team/")
    expect(getTeamMemEntrypoint("/mem/project")).to_equal("/mem/project/team/MEMORY.md")
```

</details>

### Supporting team-memory containment behavior

#### should validate write paths with string and realpath containment

- Validate safe, escaping, and symlink-escaping writes

<details>
<summary>Executable SSpec</summary>

```simple
it "should validate write paths with string and realpath containment":
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

#### should validate relative keys against the team directory

- Join a relative key and reject traversal

<details>
<summary>Executable SSpec</summary>

```simple
it "should validate relative keys against the team directory":
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

#### should classify team memory files only when enabled

- Check enabled and disabled file detection

<details>
<summary>Executable SSpec</summary>

```simple
it "should classify team memory files only when enabled":
    step("Check enabled and disabled file detection")
    expect(isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", true, true)).to_equal(true)
    expect(isTeamMemFile("/mem/project/team/a.md", "/mem/project/team/", false, true)).to_equal(false)
    expect(isTeamMemFile("/mem/project/team-evil/a.md", "/mem/project/team/", true, true)).to_equal(false)
```

</details>

### Supporting team-memory realpath behavior

#### should fail closed for dangerous realpath states

- Classify filesystem containment status

<details>
<summary>Executable SSpec</summary>

```simple
it "should fail closed for dangerous realpath states":
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
    expect(teamMemPathsSourceLinesModeled()).to_equal(292)
```

</details>

## Execution Status

The executable spec and this mirrored manual were updated statically. No
runtime was invoked, 0 scenarios were executed, and no PASS is claimed.
