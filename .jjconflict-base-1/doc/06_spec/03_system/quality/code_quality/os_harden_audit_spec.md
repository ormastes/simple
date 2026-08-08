# Os Harden Audit Specification

> 1. "fn syscall handler

<!-- sdn-diagram:id=os_harden_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_harden_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_harden_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_harden_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Harden Audit Specification

## Scenarios

### OS hardening audit

#### passes complete fixture evidence and reports static regressions

1. "fn syscall handler

2. "             cap check
   - Expected: rt_file_write_text(root + "/src/os/kernel/ipc/syscall.spl", syscall) is true
   - Expected: rt_file_write_text(root + "/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl", "MirInstKind.Intrinsic(nil, \"bounds_check\"\n") is true
   - Expected: rt_file_write_text(root + "/src/compiler/50.mir/mir_lowering_stmts.spl", "# none\n") is true
   - Expected: rt_file_write_text(root + "/src/runtime/runtime.c", "__simple_intrinsic_bounds_check\n") is true
   - Expected: rt_file_write_text(root + "/src/runtime/runtime.h", "__simple_intrinsic_bounds_check\n") is true
   - Expected: rt_file_write_text(root + "/build/multiarch/x86_64/canary_runtime.json", "{\"differs_across_reboots\": true}\n") is true
   - Expected: rt_file_write_text(root + "/build/multiarch/x86_64/text_write_trap.json", "{\"trap_observed\": true}\n") is true
   - Expected: good.2 equals `0`
   - Expected: rt_file_write_text(root + "/src/app/bad.spl", "@nocheck\nuse os.kernel.arch.x86_64.boot\n") is true
   - Expected: rt_file_write_text(root + "/src/os/kernel/vm_bad.spl", "val flags = VmFlags(bits: VM_WRITABLE)\n") is true
   - Expected: rt_file_write_text(root + "/src/os/kernel/ipc/syscall.spl", "fn syscall_handler(args):\n    match args.id:\n        case 1 # open:\n            return 0\n") is true
   - Expected: bad.2 equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_os_harden_audit_spec"
val (_clean_out, _clean_err, _clean_code) = rt_process_run("/bin/sh", ["-c", "rm -rf " + root + " && mkdir -p " + root + "/src/os/kernel/ipc " + root + "/src/compiler/50.mir " + root + "/src/runtime " + root + "/build/multiarch/x86_64"])
val syscall =
    "fn syscall_handler(args):\n" +
    "    match args.id:\n" +
    "        case 1 # open:\n" +
    "            _cap_check(args)\n" +
    "        case 2 # always allowed:\n" +
    "            return 0\n"
expect(rt_file_write_text(root + "/src/os/kernel/ipc/syscall.spl", syscall)).to_equal(true)
expect(rt_file_write_text(root + "/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl", "MirInstKind.Intrinsic(nil, \"bounds_check\"\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/compiler/50.mir/mir_lowering_stmts.spl", "# none\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/runtime/runtime.c", "__simple_intrinsic_bounds_check\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/runtime/runtime.h", "__simple_intrinsic_bounds_check\n")).to_equal(true)
expect(rt_file_write_text(root + "/build/multiarch/x86_64/canary_runtime.json", "{\"differs_across_reboots\": true}\n")).to_equal(true)
expect(rt_file_write_text(root + "/build/multiarch/x86_64/text_write_trap.json", "{\"trap_observed\": true}\n")).to_equal(true)

val good = run_audit(root, root + "/good_report.json")
expect(good.2).to_equal(0)
val good_report = rt_file_read_text(root + "/good_report.json")
expect(good_report).to_contain("\"all_arch_pass\": true")
expect(good_report).to_contain("\"cap_check_coverage_pct\": 100")

expect(rt_file_write_text(root + "/src/app/bad.spl", "@nocheck\nuse os.kernel.arch.x86_64.boot\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/os/kernel/vm_bad.spl", "val flags = VmFlags(bits: VM_WRITABLE)\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/os/kernel/ipc/syscall.spl", "fn syscall_handler(args):\n    match args.id:\n        case 1 # open:\n            return 0\n")).to_equal(true)

val bad = run_audit(root, root + "/bad_report.json")
expect(bad.2).to_equal(1)
val bad_report = rt_file_read_text(root + "/bad_report.json")
expect(bad_report).to_contain("\"all_arch_pass\": false")
expect(bad_report).to_contain("\"unsafe_outside_hal\": 1")
expect(bad_report).to_contain("\"direct_arch_imports_outside_arch\": 1")
expect(bad_report).to_contain("\"wx_violations\": 1")
expect(bad_report).to_contain("\"syscall_variants_uncovered\": 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/os_harden_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OS hardening audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
