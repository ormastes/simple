# Accessor optional/concrete storage mismatch

Status: source repair; executable regression pending an authorized rebuilt self-hosted producer.

The preserved daemon diagnostic `/tmp/simple-daemonhost15-lldb-diag-20261030/lldb-session.log`
stopped worker 1425227 at `lower_accessor_read + 2980` (0x805b04), SIGSEGV at
0xf198715900000000. Debugger exit zero is not program success; subsequent signal 9
was intentional cleanup. No diagnostic retry or compiler rebuild was used for this diagnosis.

The retained stage2-admitted binary constructs `Some(ret)` through `rt_enum_new`
at 0x80596c. Its runtime writes enum ID 1 and discriminant 0xf1987159 as two
32-bit fields at offset +8 (0x215cea0), and the real payload at +16.
The generated HirType copy reads offset +8 as the nested Span pointer, producing
0xf198715900000001, clears the tag, and faults. This identifies an enum header,
not evidence of allocator corruption.

`HirExpr.type_` is concrete HirType with authoritative `has_type_`; accessor
lowering still passed `returned: HirType?`. Repair uses concrete Error placeholder
and an explicit presence flag. Function metadata assigns the actual return and
sets presence; absent/nonfunction metadata still yields a call with no inferred type.
Accessor lookup and nil rejection paths are unchanged.

Regression: `test/01_unit/compiler/hir/accessor_return_storage_spec.spl` exercises
production lowering with declared/inferred function return metadata, absent metadata,
and nonfunction metadata. Native execution remains unperformed. Source review and
static guards are not runtime admission, and no Phase 2/3/4 result is upgraded.

Separate open validation defect: [optional-to-concrete acceptance](optional_concrete_constructor_validation_2026-10-30.md).
