# Runtime Security Specification

> Tests covering extension runtime: path containment, extension runtime: default-deny permission enforcement, extension runtime: process_spawn enforced at command dispatch for worker-placed extensions, extension runtime: crash-loop containment, extension runtime: the starts_with path hazard is fixed at the runtime-dispatch seam, extension runtime: runtime-policy helper outputs (regression pin), extension runtime: real symlink resolution (lane F3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Security Specification

## Scenarios

### extension runtime: path containment

#### reports a genuine child path as contained in its root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a genuine child path as contained in its root
   - Expected: path_contained_in("/root/a", "/root") is true
   - Expected: path_contained_in("/root", "/root") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a genuine child path as contained in its root")
expect(path_contained_in("/root/a", "/root")).to_equal(true)
expect(path_contained_in("/root", "/root")).to_equal(true)
```

</details>

#### does NOT report a string-prefix sibling as contained (the starts_with hazard)

- does NOT report a string-prefix sibling as contained (the starts_with hazard)
   - Expected: path_contained_in("/root-evil/x", "/root") is false
   - Expected: path_contained_in("/root-evil", "/root") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does NOT report a string-prefix sibling as contained (the starts_with hazard)")
expect(path_contained_in("/root-evil/x", "/root")).to_equal(false)
expect(path_contained_in("/root-evil", "/root")).to_equal(false)
```

</details>

#### canonicalizes '.' and collapses resolvable '..' segments

- canonicalizes '.' and collapses resolvable '..' segments
   - Expected: path_canonicalize("/root/./a/../b") equals `/root/b`
   - Expected: path_canonicalize("/a/../../b") equals `/b`
   - Expected: path_canonicalize("a/./b/") equals `a/b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("canonicalizes '.' and collapses resolvable '..' segments")
expect(path_canonicalize("/root/./a/../b")).to_equal("/root/b")
expect(path_canonicalize("/a/../../b")).to_equal("/b")
expect(path_canonicalize("a/./b/")).to_equal("a/b")
```

</details>

#### keeps an unresolvable leading '..' on a relative path (nothing to resolve against)

- keeps an unresolvable leading '..' on a relative path (nothing to resolve against)
   - Expected: path_canonicalize("a/../../etc") equals `../etc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an unresolvable leading '..' on a relative path (nothing to resolve against)")
expect(path_canonicalize("a/../../etc")).to_equal("../etc")
```

</details>

#### rejects an absolute manifest entry path

- rejects an absolute manifest entry path
   - Expected: "absolute entry" equals `should have been rejected`
   - Expected: reason contains `absolute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an absolute manifest entry path")
match path_resolve_entry("/pkg/root", "/etc/passwd"):
    case Ok(_):
        expect("absolute entry").to_equal("should have been rejected")
    case Err(reason):
        expect(reason.contains("absolute")).to_equal(true)
```

</details>

#### rejects a relative manifest entry path that escapes the package root

- rejects a relative manifest entry path that escapes the package root
   - Expected: "escaping entry" equals `should have been rejected`
   - Expected: reason contains `escapes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a relative manifest entry path that escapes the package root")
match path_resolve_entry("/pkg/root", "a/../../etc/passwd"):
    case Ok(_):
        expect("escaping entry").to_equal("should have been rejected")
    case Err(reason):
        expect(reason.contains("escapes")).to_equal(true)
```

</details>

#### resolves a genuine relative manifest entry path under the package root

- resolves a genuine relative manifest entry path under the package root
   - Expected: resolved equals `/pkg/root/src/main.spl`
   - Expected: "valid entry" equals `should have resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves a genuine relative manifest entry path under the package root")
match path_resolve_entry("/pkg/root", "src/main.spl"):
    case Ok(resolved):
        expect(resolved).to_equal("/pkg/root/src/main.spl")
    case Err(_):
        expect("valid entry").to_equal("should have resolved")
```

</details>

### extension runtime: default-deny permission enforcement

#### denies a capability the manifest never granted

- denies a capability the manifest never granted
   - Expected: "process_spawn" equals `should have been denied`
   - Expected: reason contains `process_spawn`
   - Expected: reason contains `denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies a capability the manifest never granted")
val perms = extension_permissions_none()
match runtime_check_permission(perms, "process_spawn"):
    case Ok(_):
        expect("process_spawn").to_equal("should have been denied")
    case Err(reason):
        expect(reason.contains("process_spawn")).to_equal(true)
        expect(reason.contains("denied")).to_equal(true)
```

</details>

#### denies an unrecognized capability name (default-deny, not default-allow)

- denies an unrecognized capability name (default-deny, not default-allow)
   - Expected: "unknown capability" equals `should have been denied`
   - Expected: reason contains `denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an unrecognized capability name (default-deny, not default-allow)")
val perms = extension_permissions_none()
match runtime_check_permission(perms, "not_a_real_capability"):
    case Ok(_):
        expect("unknown capability").to_equal("should have been denied")
    case Err(reason):
        expect(reason.contains("denied")).to_equal(true)
```

</details>

#### grants a capability the manifest explicitly declares

- grants a capability the manifest explicitly declares
   - Expected: "granted workspace_write" equals `should have been allowed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("grants a capability the manifest explicitly declares")
var perms = extension_permissions_none()
perms.workspace_write = true
match runtime_check_permission(perms, "workspace_write"):
    case Ok(_):
        pass_do_nothing
    case Err(_):
        expect("granted workspace_write").to_equal("should have been allowed")
```

</details>

### extension runtime: process_spawn enforced at command dispatch for worker-placed extensions

#### a worker extension without process_spawn cannot dispatch (default-deny)

- a worker extension without process_spawn cannot dispatch (default-deny)
   - Expected: "denied worker dispatch" equals `should have failed`
   - Expected: reason contains `process_spawn`
   - Expected: reason contains `denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a worker extension without process_spawn cannot dispatch (default-deny)")
var host = ExtensionHost.new()
host.register_manifest(worker_denied_manifest(), "<test>")
host.register_command_handler("worker-ext-denied", "worker.run", "Worker Run", worker_handler)
match host.dispatch_command("worker.run", "x"):
    case Ok(_):
        expect("denied worker dispatch").to_equal("should have failed")
    case Err(reason):
        expect(reason.contains("process_spawn")).to_equal(true)
        expect(reason.contains("denied")).to_equal(true)
```

</details>

#### a worker extension with process_spawn granted dispatches normally

- a worker extension with process_spawn granted dispatches normally
   - Expected: out equals `worker-ran:x`
   - Expected: "granted worker dispatch" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a worker extension with process_spawn granted dispatches normally")
var host = ExtensionHost.new()
host.register_manifest(worker_granted_manifest(), "<test>")
host.register_command_handler("worker-ext-granted", "worker.run", "Worker Run", worker_handler)
match host.dispatch_command("worker.run", "x"):
    case Ok(out):
        expect(out).to_equal("worker-ran:x")
    case Err(_):
        expect("granted worker dispatch").to_equal("should have succeeded")
```

</details>

### extension runtime: crash-loop containment

#### disables an extension after 3 consecutive handler failures, then runtime_reenable clears it

- disables an extension after 3 consecutive handler failures, then runtime_reenable clears it
   - Expected: "failure 1" equals `should have failed`
   - Expected: msg equals `boom`
   - Expected: "failure 2" equals `should have failed`
   - Expected: msg equals `boom`
   - Expected: "failure 3" equals `should have failed`
   - Expected: msg equals `boom`
   - Expected: "4th dispatch" equals `should have been blocked`
   - Expected: msg contains `disabled after repeated failures`
   - Expected: host.is_active("crash-ext") is true
   - Expected: out equals `ok:5`
   - Expected: "dispatch after reenable" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("disables an extension after 3 consecutive handler failures, then runtime_reenable clears it")
var host = ExtensionHost.new()
host.register_manifest(crash_test_manifest(), "<test>")
host.register_command_handler("crash-ext", "crash.run", "Crash Run", crash_handler)
crash_test_set_should_fail(true)

match host.dispatch_command("crash.run", "1"):
    case Ok(_):
        expect("failure 1").to_equal("should have failed")
    case Err(msg):
        expect(msg).to_equal("boom")
match host.dispatch_command("crash.run", "2"):
    case Ok(_):
        expect("failure 2").to_equal("should have failed")
    case Err(msg):
        expect(msg).to_equal("boom")
match host.dispatch_command("crash.run", "3"):
    case Ok(_):
        expect("failure 3").to_equal("should have failed")
    case Err(msg):
        expect(msg).to_equal("boom")

# 4th dispatch is short-circuited by crash containment, not the handler
match host.dispatch_command("crash.run", "4"):
    case Ok(_):
        expect("4th dispatch").to_equal("should have been blocked")
    case Err(msg):
        expect(msg.contains("disabled after repeated failures")).to_equal(true)
expect(host.is_active("crash-ext")).to_equal(true)

crash_test_set_should_fail(false)
host.runtime_reenable("crash-ext")
match host.dispatch_command("crash.run", "5"):
    case Ok(out):
        expect(out).to_equal("ok:5")
    case Err(_):
        expect("dispatch after reenable").to_equal("should have succeeded")
```

</details>

#### a successful dispatch resets the consecutive-failure counter

- a successful dispatch resets the consecutive-failure counter
   - Expected: out equals `ok:3`
   - Expected: "recovered dispatch" equals `should have succeeded`
   - Expected: "failure after reset" equals `should have failed`
   - Expected: msg equals `boom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a successful dispatch resets the consecutive-failure counter")
var host = ExtensionHost.new()
host.register_manifest(crash_test_manifest(), "<test>")
host.register_command_handler("crash-ext", "crash.run", "Crash Run", crash_handler)

crash_test_set_should_fail(true)
host.dispatch_command("crash.run", "1")
host.dispatch_command("crash.run", "2")
crash_test_set_should_fail(false)
match host.dispatch_command("crash.run", "3"):
    case Ok(out):
        expect(out).to_equal("ok:3")
    case Err(_):
        expect("recovered dispatch").to_equal("should have succeeded")

# two more real failures after the reset should NOT yet disable (needs 3 in a row)
crash_test_set_should_fail(true)
host.dispatch_command("crash.run", "4")
match host.dispatch_command("crash.run", "5"):
    case Ok(_):
        expect("failure after reset").to_equal("should have failed")
    case Err(msg):
        expect(msg).to_equal("boom")
```

</details>

### extension runtime: the starts_with path hazard is fixed at the runtime-dispatch seam

#### rejects a string-prefix sibling directory as an allowed runtime root

- rejects a string-prefix sibling directory as an allowed runtime root
   - Expected: host.drain_invocation_queue() equals `1`
   - Expected: record.status equals `blocked-runtime`
   - Expected: record.reason equals `extension root not allowed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a string-prefix sibling directory as an allowed runtime root")
var host = ExtensionHost.new()
host.register_manifest(sibling_hazard_manifest(), "root-evil/ext")
host.register_command_handler("sibling-ext", "sibling.run", "Sibling Run", worker_handler)
host.set_runtime_policy(extension_runtime_policy_sandboxed(["root"]))
host.dispatch_external_command("sibling.run", "x")
expect(host.drain_invocation_queue()).to_equal(1)
val record = host.last_runtime_dispatch()
expect(record.status).to_equal("blocked-runtime")
expect(record.reason).to_equal("extension root not allowed")
```

</details>

#### allows a genuine subdirectory of the allowed root

- allows a genuine subdirectory of the allowed root
   - Expected: host.drain_invocation_queue() equals `1`
   - Expected: record.status equals `ready-sandbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows a genuine subdirectory of the allowed root")
var host = ExtensionHost.new()
host.register_manifest(good_root_manifest(), "root/ext")
host.register_command_handler("good-ext", "good.run", "Good Run", worker_handler)
host.set_runtime_policy(extension_runtime_policy_sandboxed(["root"]))
host.dispatch_external_command("good.run", "x")
expect(host.drain_invocation_queue()).to_equal(1)
val record = host.last_runtime_dispatch()
expect(record.status).to_equal("ready-sandbox")
```

</details>

### extension runtime: runtime-policy helper outputs (regression pin)

#### extension_runtime_policy_default/_sandboxed/_external_process keep their current shape

- extension_runtime_policy_default/_sandboxed/_external_process keep their current shape
   - Expected: default_policy.enabled is false
   - Expected: default_policy.allow_external_process is false
   - Expected: default_policy.allowed_roots.len() equals `0`
   - Expected: sandboxed.enabled is true
   - Expected: sandboxed.allow_external_process is false
   - Expected: sandboxed.allowed_roots.len() equals `2`
   - Expected: sandboxed.allowed_roots[0] equals `root/a`
   - Expected: external.enabled is true
   - Expected: external.allow_external_process is true
   - Expected: external.allowed_roots.len() equals `1`
   - Expected: external.allowed_roots[0] equals `root/c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extension_runtime_policy_default/_sandboxed/_external_process keep their current shape")
val default_policy = extension_runtime_policy_default()
expect(default_policy.enabled).to_equal(false)
expect(default_policy.allow_external_process).to_equal(false)
expect(default_policy.allowed_roots.len()).to_equal(0)

val sandboxed = extension_runtime_policy_sandboxed(["root/a", "root/b"])
expect(sandboxed.enabled).to_equal(true)
expect(sandboxed.allow_external_process).to_equal(false)
expect(sandboxed.allowed_roots.len()).to_equal(2)
expect(sandboxed.allowed_roots[0]).to_equal("root/a")

val external = extension_runtime_policy_external_process(["root/c"])
expect(external.enabled).to_equal(true)
expect(external.allow_external_process).to_equal(true)
expect(external.allowed_roots.len()).to_equal(1)
expect(external.allowed_roots[0]).to_equal("root/c")
```

</details>

### extension runtime: real symlink resolution (lane F3)

#### detects a symlink placed inside a sandboxed root that points outside it

- detects a symlink placed inside a sandboxed root that points outside it
   - Expected: true is true
   - Expected: true is true
   - Expected: resolved equals `path_canonicalize(outside)`
   - Expected: path_contained_in(link_path, root) is false
   - Expected: path_contained_in(resolved, root) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects a symlink placed inside a sandboxed root that points outside it")
val root = "/tmp/l6f3_symlink_root"
val outside = "/tmp/l6f3_symlink_outside"
rt_dir_remove_all(root)
rt_dir_remove_all(outside)
val root_ok = rt_dir_create_all(root)
val outside_ok = rt_dir_create_all(outside)
if not (root_ok and outside_ok):
    print("SKIP: could not create temp dirs for symlink-escape test")
    expect(true).to_equal(true)
else:
    val link_path = root + "/escape"
    val symlink_status = rt_package_create_symlink(outside, link_path)
    if symlink_status != 0:
        print("SKIP: symlink creation unavailable on this platform/sandbox (status=" + symlink_status.to_text() + ") -- path_canonicalize's real-resolution branch is untested by this case here")
        expect(true).to_equal(true)
    else:
        # A purely LEXICAL check would see "root/escape" as contained
        # in "root"; real resolution must see through the symlink to
        # its true (outside-root) target and reject it.
        val resolved = path_canonicalize(link_path)
        expect(resolved).to_equal(path_canonicalize(outside))
        expect(path_contained_in(link_path, root)).to_equal(false)
        expect(path_contained_in(resolved, root)).to_equal(false)
    rt_dir_remove_all(root)
    rt_dir_remove_all(outside)
```

</details>

#### still applies pure lexical normalization to a path that does not exist on disk

- still applies pure lexical normalization to a path that does not exist on disk
   - Expected: path_canonicalize("/l6f3-definitely-nonexistent-root/./a/../b") equals `/l6f3-definitely-nonexistent-root/b`
   - Expected: path_canonicalize("l6f3-nonexistent-relative/../../etc") equals `../etc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still applies pure lexical normalization to a path that does not exist on disk")
expect(path_canonicalize("/l6f3-definitely-nonexistent-root/./a/../b")).to_equal("/l6f3-definitely-nonexistent-root/b")
expect(path_canonicalize("l6f3-nonexistent-relative/../../etc")).to_equal("../etc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/extensions/runtime_security_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering extension runtime: path containment, extension runtime: default-deny permission enforcement, extension runtime: process_spawn enforced at command dispatch for worker-placed extensions, extension runtime: crash-loop containment, extension runtime: the starts_with path hazard is fixed at the runtime-dispatch seam, extension runtime: runtime-policy helper outputs (regression pin), extension runtime: real symlink resolution (lane F3).
- extension runtime: path containment
- extension runtime: default-deny permission enforcement
- extension runtime: process_spawn enforced at command dispatch for worker-placed extensions
- extension runtime: crash-loop containment
- extension runtime: the starts_with path hazard is fixed at the runtime-dispatch seam
- extension runtime: runtime-policy helper outputs (regression pin)
- extension runtime: real symlink resolution (lane F3)

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `43206d580cab19cc17fb3eac79a7bf6259bfe58d83c0e70d57eee577d676cdad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43206d580cab19cc17fb3eac79a7bf6259bfe58d83c0e70d57eee577d676cdad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43206d580cab19cc17fb3eac79a7bf6259bfe58d83c0e70d57eee577d676cdad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/editor/extensions/runtime_security_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/extensions/runtime_security_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/extensions/runtime_security_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/extensions/runtime_security_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/extensions/runtime_security_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/extensions/runtime_security_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a genuine child path as contained in its root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/runtime_security_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT report a string-prefix sibling as contained (the starts_with hazard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/runtime_security_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'canonicalizes '.' and collapses resolvable '..' segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
