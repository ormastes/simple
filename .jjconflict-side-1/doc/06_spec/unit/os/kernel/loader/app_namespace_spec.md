# App Namespace Specification

> Tests covering SimpleOS app namespace contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Namespace Specification

## Scenarios

### SimpleOS app namespace contract

#### exposes the default process filesystem paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes the default process filesystem paths
   - Expected: ns.root equals `/`
   - Expected: ns.cwd equals `/`
   - Expected: ns.mount_view equals `["/bin", "/usr/bin", "/sys/apps", "/lib", "/usr/lib", "/tmp", "/home", "/svc"]`
   - Expected: ns.cap_dirs equals `["/svc"]`
   - Expected: ns.library_paths equals `["/lib", "/usr/lib", "/usr/lib/simple"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the default process filesystem paths")
val ns = app_namespace_default()
expect(ns.root).to_equal("/")
expect(ns.cwd).to_equal("/")
expect(ns.mount_view).to_equal(["/bin", "/usr/bin", "/sys/apps", "/lib", "/usr/lib", "/tmp", "/home", "/svc"])
expect(ns.cap_dirs).to_equal(["/svc"])
expect(ns.library_paths).to_equal(["/lib", "/usr/lib", "/usr/lib/simple"])
```

</details>

#### resolves relative paths from each process cwd

- resolves relative paths from each process cwd
   - Expected: home_ns != nil is true
   - Expected: tmp_ns != nil is true
   - Expected: app_namespace_resolve_path(home_ns.unwrap(), "notes.txt") equals `Some("/home/alice/notes.txt")`
   - Expected: app_namespace_resolve_path(tmp_ns.unwrap(), "notes.txt") equals `Some("/tmp/notes.txt")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves relative paths from each process cwd")
val base = app_namespace_default()
val home_ns = app_namespace_with_cwd(base, "/home/alice")
val tmp_ns = app_namespace_with_cwd(base, "/tmp")

expect(home_ns != nil).to_equal(true)
expect(tmp_ns != nil).to_equal(true)
expect(app_namespace_resolve_path(home_ns.unwrap(), "notes.txt")).to_equal(Some("/home/alice/notes.txt"))
expect(app_namespace_resolve_path(tmp_ns.unwrap(), "notes.txt")).to_equal(Some("/tmp/notes.txt"))
```

</details>

#### prevents dot-dot from escaping the process root

- prevents dot-dot from escaping the process root
   - Expected: app_namespace_resolve_path(ns, "../../bin/sh") equals `nil`
   - Expected: app_namespace_resolve_path(ns, "/tmp/../../bin/sh") equals `nil`
   - Expected: app_namespace_resolve_path(ns, "/tmp/../bin/sh") equals `Some("/bin/sh")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prevents dot-dot from escaping the process root")
val ns = app_namespace_default()
expect(app_namespace_resolve_path(ns, "../../bin/sh")).to_equal(nil)
expect(app_namespace_resolve_path(ns, "/tmp/../../bin/sh")).to_equal(nil)
expect(app_namespace_resolve_path(ns, "/tmp/../bin/sh")).to_equal(Some("/bin/sh"))
```

</details>

#### keeps resolved paths under a non-default root

- keeps resolved paths under a non-default root
   - Expected: ns != nil is true
   - Expected: app_namespace_resolve_path(ns.unwrap(), "state.db") equals `Some("/sys/apps/browser_demo/home/app/state.db")`
   - Expected: app_namespace_resolve_path(ns.unwrap(), "../../../escape") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps resolved paths under a non-default root")
val ns = app_namespace_create("/sys/apps/browser_demo", "/home/app", ["/home", "/lib"], ["/svc"], ["/lib"])
expect(ns != nil).to_equal(true)
expect(app_namespace_resolve_path(ns.unwrap(), "state.db")).to_equal(Some("/sys/apps/browser_demo/home/app/state.db"))
expect(app_namespace_resolve_path(ns.unwrap(), "../../../escape")).to_equal(nil)
```

</details>

#### orders library lookup by process paths before explicit manifest paths

- orders library lookup by process paths before explicit manifest paths
   - Expected: candidates equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders library lookup by process paths before explicit manifest paths")
val ns = app_namespace_default()
val candidates = app_namespace_library_candidates(ns, "libui.smf", ["/sys/apps/browser_demo/lib/libui.smf", "local/libextra.smf"])

expect(candidates).to_equal([
    "/lib/libui.smf",
    "/usr/lib/libui.smf",
    "/usr/lib/simple/libui.smf",
    "/sys/apps/browser_demo/lib/libui.smf",
    "/local/libextra.smf"
])
```

</details>

#### resolves explicit absolute library names before manifest extras

- resolves explicit absolute library names before manifest extras
   - Expected: candidates equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves explicit absolute library names before manifest extras")
val ns = app_namespace_default()
val candidates = app_namespace_library_candidates(ns, "/sys/apps/browser_demo/lib/libui.smf", ["/usr/lib/libfallback.smf"])

expect(candidates).to_equal([
    "/sys/apps/browser_demo/lib/libui.smf",
    "/usr/lib/libfallback.smf"
])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/app_namespace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS app namespace contract.
- SimpleOS app namespace contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da39eb9937c168ff2c59cda36564729ded4234d9ee1ed757dfde4a84bd217e37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da39eb9937c168ff2c59cda36564729ded4234d9ee1ed757dfde4a84bd217e37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da39eb9937c168ff2c59cda36564729ded4234d9ee1ed757dfde4a84bd217e37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/loader/app_namespace_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/app_namespace_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/app_namespace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/app_namespace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/app_namespace_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the default process filesystem paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/app_namespace_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves relative paths from each process cwd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/app_namespace_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevents dot-dot from escaping the process root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
