# std.io_runtime File-Read Surface

> Regression guard for the `std.io_runtime` re-export shim

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.io_runtime File-Read Surface

Regression guard for the `std.io_runtime` re-export shim

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/io_runtime_read_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression guard for the `std.io_runtime` re-export shim
(`src/lib/io_runtime.spl`).

A name that `std.io_runtime` cannot supply does not fail at the `use`
site — an unresolved `use` is only a WARN, so the module loads at exit 0
and the breakage surfaces only later, as
`semantic: function <name> not found` at the first call site.

What actually gates resolution here is the **declaration in the tier
module** `src/lib/nogc_sync_mut/io_runtime.spl`, not the explicit name
list in the `src/lib/io_runtime.spl` shim. Verified by sabotage: deleting
a name from the shim's export list leaves this spec fully GREEN, while
renaming the `pub fn` in the tier module turns it RED with exactly the
`function ... not found` text above. So assert against the tier
declaration, and do not treat the shim list as the guard.

That is exactly how `test/03_system/compiler/stage3_segfault_fix_spec.spl`
sat with 14 of 18 examples red on `function read_text_file not found`
without anyone noticing: `read_text_file` was never a `std.io_runtime`
name (it is declared only in the separate seed tree at
`src/compiler_rust/lib/std/src/io/fs_helpers.spl`, with a different
`Result<text, text>` return type).

This spec calls each read name for real and asserts on content, so losing
one of the tier declarations turns this file red instead of silently
rerouting a caller into a not-found at its first call site.

## Scenarios

### std.io_runtime file-read surface resolves and reads

#### file_exists reports true for a repo file and false for a missing one

- file_exists reports true for a repo file and false for a missing one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("file_exists reports true for a repo file and false for a missing one")
assert_true(file_exists("src/lib/io_runtime.spl"))
assert_false(file_exists("definitely_not_a_real_file_xyz.toml"))
```

</details>

#### file_read returns non-empty content for a known repo file

- file_read returns non-empty content for a known repo file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("file_read returns non-empty content for a known repo file")
val content = file_read("src/lib/io_runtime.spl")
expect(content).to_contain("export use nogc_sync_mut.io_runtime")
```

</details>

#### read_file returns the same content as file_read

- read_file returns the same content as file_read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read_file returns the same content as file_read")
val content = read_file("src/lib/io_runtime.spl")
expect(content).to_contain("export use nogc_sync_mut.io_runtime")
```

</details>

#### read_file_text returns the same content as file_read

- read_file_text returns the same content as file_read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read_file_text returns the same content as file_read")
val content = read_file_text("src/lib/io_runtime.spl")
expect(content).to_contain("export use nogc_sync_mut.io_runtime")
```

</details>

#### read_file_text reaches the tier module the shim re-exports from

- read_file_text reaches the tier module the shim re-exports from


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read_file_text reaches the tier module the shim re-exports from")
val content = read_file_text("src/lib/nogc_sync_mut/io_runtime.spl")
expect(content).to_contain("pub fn read_file_text")
```

</details>

#### hash_text is a bare passthrough to rt_hash_text

- hash_text is a bare passthrough to rt_hash_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hash_text is a bare passthrough to rt_hash_text")
assert_equal(hash_text(""), rt_hash_text(""))
assert_equal(hash_text("simple"), rt_hash_text("simple"))
assert_equal(hash_text("src/lib/io_runtime.spl"), rt_hash_text("src/lib/io_runtime.spl"))
```

</details>

#### time_now_monotonic_ms is a bare passthrough to rt_time_now_monotonic_ms (monotonic non-decreasing)

- time_now_monotonic_ms is a bare passthrough to rt_time_now_monotonic_ms (monotonic non-decreasing)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("time_now_monotonic_ms is a bare passthrough to rt_time_now_monotonic_ms (monotonic non-decreasing)")
val a = rt_time_now_monotonic_ms()
val b = time_now_monotonic_ms()
val c = rt_time_now_monotonic_ms()
assert_true(b >= a)
assert_true(c >= b)
```

</details>

#### shell_exec is a bare passthrough to rt_shell_exec

- shell_exec is a bare passthrough to rt_shell_exec


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shell_exec is a bare passthrough to rt_shell_exec")
assert_equal(shell_exec("echo simple"), rt_shell_exec("echo simple"))
assert_equal(shell_exec("printf ok"), rt_shell_exec("printf ok"))
```

</details>

#### file_rename is a bare passthrough to rt_file_rename

- file_rename is a bare passthrough to rt_file_rename


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("file_rename is a bare passthrough to rt_file_rename")
val a1 = "/tmp/io_runtime_spec_rename_a1.txt"
val a2 = "/tmp/io_runtime_spec_rename_a2.txt"
val b1 = "/tmp/io_runtime_spec_rename_b1.txt"
val b2 = "/tmp/io_runtime_spec_rename_b2.txt"
shell_exec("touch {a1}")
shell_exec("touch {b1}")
assert_equal(file_rename(a1, a2), rt_file_rename(b1, b2))
assert_true(file_exists(a2))
assert_true(file_exists(b2))
shell_exec("rm -f {a2} {b2}")
```

</details>

#### process_run_timeout is a bare passthrough to rt_process_run_timeout

- process_run_timeout is a bare passthrough to rt_process_run_timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("process_run_timeout is a bare passthrough to rt_process_run_timeout")
val r1 = process_run_timeout("echo", ["simple"], 5000)
val r2 = rt_process_run_timeout("echo", ["simple"], 5000)
assert_equal(r1, r2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7a0337d5f594c72be3911189667b84310ebbe537750880f6b8e86f055773f18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7a0337d5f594c72be3911189667b84310ebbe537750880f6b8e86f055773f18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7a0337d5f594c72be3911189667b84310ebbe537750880f6b8e86f055773f18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/lib/io_runtime_read_surface_spec.spl
mirror: doc/06_spec/03_system/lib/io_runtime_read_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/io_runtime_read_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/lib/io_runtime_read_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/lib/io_runtime_read_surface_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_exists reports true for a repo file and false for a missing one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/io_runtime_read_surface_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_read returns non-empty content for a known repo file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/io_runtime_read_surface_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_file returns the same content as file_read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
