# simpleos_host_link_plan_spec

> SimpleOS host link plan — first-class host parity contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_host_link_plan_spec

SimpleOS host link plan — first-class host parity contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/simpleos_host_link_plan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SimpleOS host link plan — first-class host parity contract.

AC-12 (simpleos-alpine-harden-musl-busybox): the compiler must treat
"simpleos" as a first-class unix-like host, exactly like linux/freebsd —
NOT fall through to the empty "unknown OS" plan.

The proof: for os="simpleos" the per-host link data (libraries, crt search
dirs, dynamic-loader candidates, lib dirs) is POPULATED, while a genuinely
unknown OS ("plan9") still returns empty. That difference is what "simple
works on simpleos like other host" means concretely.

REGRESSION GUARD: linux and freebsd plans must be unchanged (additive only).

## Scenarios

### SimpleOS host link plan

#### simpleos is a populated first-class host (not the empty fallback)

#### links libc (c) like other unix hosts

- links libc (c) like other unix hosts
   - Expected: default_libraries("simpleos") contains `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("links libc (c) like other unix hosts")
expect(default_libraries("simpleos").contains("c")).to_equal(true)
```

</details>

#### links pthread

- links pthread
   - Expected: default_libraries("simpleos") contains `pthread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("links pthread")
expect(default_libraries("simpleos").contains("pthread")).to_equal(true)
```

</details>

#### has a non-empty crt search path

- has a non-empty crt search path
   - Expected: default_crt_search_dirs("simpleos", "x86_64").len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has a non-empty crt search path")
expect(default_crt_search_dirs("simpleos", "x86_64").len() > 0).to_equal(true)
```

</details>

#### has a dynamic loader candidate

- has a dynamic loader candidate
   - Expected: default_dynamic_linker_candidates("simpleos", "x86_64").len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has a dynamic loader candidate")
expect(default_dynamic_linker_candidates("simpleos", "x86_64").len() > 0).to_equal(true)
```

</details>

#### uses the unix lib dirs (not the windows empty set)

- uses the unix lib dirs (not the windows empty set)
   - Expected: default_library_dirs("simpleos").len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the unix lib dirs (not the windows empty set)")
expect(default_library_dirs("simpleos").len() > 0).to_equal(true)
```

</details>

#### platform_defaults yields a populated plan

- platform_defaults yields a populated plan
   - Expected: p.libraries.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("platform_defaults yields a populated plan")
val p = platform_defaults("simpleos", "x86_64")
expect(p.libraries.len() > 0).to_equal(true)
```

</details>

#### an unknown OS stays empty — proves simpleos genuinely crossed into host status

#### unknown OS has no libraries

- unknown OS has no libraries
   - Expected: default_libraries("plan9").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown OS has no libraries")
expect(default_libraries("plan9").len()).to_equal(0)
```

</details>

#### unknown OS has no loader candidates

- unknown OS has no loader candidates
   - Expected: default_dynamic_linker_candidates("plan9", "x86_64").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown OS has no loader candidates")
expect(default_dynamic_linker_candidates("plan9", "x86_64").len()).to_equal(0)
```

</details>

#### regression guard — linux unchanged

#### linux still links c/pthread/dl/m

- linux still links c/pthread/dl/m
   - Expected: libs contains `"c") and libs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("linux still links c/pthread/dl/m")
val libs = default_libraries("linux")
expect(libs.contains("c") and libs.contains("dl")).to_equal(true)
```

</details>

#### linux x86_64 loader unchanged

- linux x86_64 loader unchanged
   - Expected: default_dynamic_linker_candidates("linux", "x86_64") contains `/lib64/ld-linux-x86-64.so.2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("linux x86_64 loader unchanged")
expect(default_dynamic_linker_candidates("linux", "x86_64").contains("/lib64/ld-linux-x86-64.so.2")).to_equal(true)
```

</details>

#### regression guard — freebsd unchanged

#### freebsd still uses ld-elf.so.1

- freebsd still uses ld-elf.so.1
   - Expected: default_dynamic_linker_candidates("freebsd", "x86_64") contains `/libexec/ld-elf.so.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("freebsd still uses ld-elf.so.1")
expect(default_dynamic_linker_candidates("freebsd", "x86_64").contains("/libexec/ld-elf.so.1")).to_equal(true)
```

</details>

#### freebsd links c/pthread/m

- freebsd links c/pthread/m
   - Expected: default_libraries("freebsd") contains `pthread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("freebsd links c/pthread/m")
expect(default_libraries("freebsd").contains("pthread")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4cb026ccbbd22b97c1a8d53ae18a3f59f6f395b2af6a44b9518ed8bad581340`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4cb026ccbbd22b97c1a8d53ae18a3f59f6f395b2af6a44b9518ed8bad581340`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4cb026ccbbd22b97c1a8d53ae18a3f59f6f395b2af6a44b9518ed8bad581340`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/simpleos_host_link_plan_spec.spl
mirror: doc/06_spec/01_unit/compiler/simpleos_host_link_plan_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/simpleos_host_link_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/simpleos_host_link_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/simpleos_host_link_plan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/simpleos_host_link_plan_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links libc (c) like other unix hosts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/simpleos_host_link_plan_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links pthread' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/simpleos_host_link_plan_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a non-empty crt search path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
