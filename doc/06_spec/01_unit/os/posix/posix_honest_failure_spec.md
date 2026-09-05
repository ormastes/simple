# POSIX Honest-Failure Specification

> Lane P5 (POSIX truth) forbids stubs that silently report fake success for a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# POSIX Honest-Failure Specification

Lane P5 (POSIX truth) forbids stubs that silently report fake success for a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/posix_honest_failure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lane P5 (POSIX truth) forbids stubs that silently report fake success for a
facility the SimpleOS L4 syscall path does not actually implement. This spec
pins two honest-failure contracts on the guest libc shim
(`src/os/libc/simpleos_libc.c`):

1. `mmap()` on the SimpleOS syscall path (the non-Linux-host branch — the
   Linux-host branch is a real passthrough syscall and is out of scope) must
   fail closed with `EOPNOTSUPP` for a writable `MAP_SHARED` request and for
   any fd-backed (file-backed) request, instead of silently discarding
   `flags`/`fd`/`offset` and handing back an anonymous private mapping that
   looks like success but is neither shared nor file-backed. See
   `doc/02_requirements/os/posix_profiles.md` and
   `src/os/posix/mod.spl` ("writable POSIX shared-memory mmap" is documented
   as NOT supported by design).
2. `pthread_create()` must report `ENOSYS`, never a fake success code, since
   SimpleOS has no kernel thread support behind the guest libc yet.

The guest-only `mmap()` branch only executes when `running_on_linux_host()`
is false (real SimpleOS kernel, not a host Linux ELF run for cross-toolchain
bring-up), so it cannot be exercised by spawning a host-compiled binary from
this spec. Instead this spec pins the honest-failure contract directly on
the shipped source text, so a regression that reintroduces the silent
downgrade is caught the moment the source changes back.

## Scenarios

### mmap honest failure on the SimpleOS syscall path

#### loads the guest libc shim source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads the guest libc shim source
   - Expected: src.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads the guest libc shim source")
val src = libc_source()
expect(src.len() > 0).to_equal(true)
```

</details>

#### rejects a writable MAP_SHARED request with EOPNOTSUPP

- rejects a writable MAP_SHARED request with EOPNOTSUPP


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a writable MAP_SHARED request with EOPNOTSUPP")
val src = libc_source()
expect(src).to_contain("(flags & MAP_SHARED) != 0 && (prot & PROT_WRITE) != 0")
expect(src).to_contain("errno = EOPNOTSUPP;")
```

</details>

#### rejects an fd-backed (file-backed) mmap request instead of silently going anonymous

- rejects an fd-backed (file-backed) mmap request instead of silently going anonymous


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an fd-backed (file-backed) mmap request instead of silently going anonymous")
val src = libc_source()
expect(src).to_contain("if (fd >= 0)")
```

</details>

#### no longer discards flags and fd unconditionally before the syscall

- no longer discards flags and fd unconditionally before the syscall
   - Expected: src does not contain `(void)flags; (void)fd; (void)offset;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no longer discards flags and fd unconditionally before the syscall")
val src = libc_source()
# The old lie: `(void)flags; (void)fd; (void)offset;` right before
# dispatching syscall 10 unconditionally, with no honesty check
# in between. The fixed source keeps `(void)offset;` alone (offset
# is genuinely meaningless once file-backed requests are rejected)
# but must not still contain the three-in-one discard.
expect(src).to_contain("(void)offset;")
expect(src.contains("(void)flags; (void)fd; (void)offset;")).to_equal(false)
```

</details>

### pthread_create honest failure

#### loads the guest pthread shim source

- loads the guest pthread shim source
   - Expected: src.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads the guest pthread shim source")
val src = pthread_source()
expect(src.len() > 0).to_equal(true)
```

</details>

#### reports ENOSYS instead of faking a created thread

- reports ENOSYS instead of faking a created thread


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports ENOSYS instead of faking a created thread")
val src = pthread_source()
expect(src).to_contain("int pthread_create(pthread_t *thread, const pthread_attr_t *attr,")
expect(src).to_contain("return ENOSYS;")
```

</details>

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

- Canonical SPipe generation for source `6db435c3b82c3a6b8af45fa62532a82b58b6e5ef6d7b3f782067ac8a8c059ba5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6db435c3b82c3a6b8af45fa62532a82b58b6e5ef6d7b3f782067ac8a8c059ba5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6db435c3b82c3a6b8af45fa62532a82b58b6e5ef6d7b3f782067ac8a8c059ba5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/posix/posix_honest_failure_spec.spl
mirror: doc/06_spec/01_unit/os/posix/posix_honest_failure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/posix/posix_honest_failure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/posix/posix_honest_failure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/posix/posix_honest_failure_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the guest libc shim source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/posix/posix_honest_failure_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a writable MAP_SHARED request with EOPNOTSUPP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/posix/posix_honest_failure_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an fd-backed (file-backed) mmap request instead of silently going anonymous' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
