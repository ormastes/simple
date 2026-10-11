# Provider callable relocation passes a boxed optional as HirType

Status: **causal GDB evidence captured; source repair pending coordinated native verification**.

## Frozen failure

The release aggregate source is `c2a88e77ec2847e63cdc540e726ed38f11e6a88b`; its pure-Simple producer SHA-256 is `e05e69a2539bb417eda6519d98666ed244f93fdb7db38e92224f58e80f8af178`, executed from the immutable capsule `/tmp/release-owned-cycle2-runtime-capsules/e05e69a2539bb417eda6519d98666ed244f93fdb7db38e92224f58e80f8af178/simple`. The unchanged `nested_enum_field_owner/indexed_layout.spl` fixture reached HIR and monomorphization before MIR crashed; its original ARM build exited 117. This is a compiler crash, not a fixture assertion or qualified native artifact.

One GDB probe used the exact producer/source, copied private caches, explicit entry closure, host-gpu runtime capsule, and the continue-until-fault helper that follows shell and worker inferiors. CPU affinity was 12–13; core dumps were disabled. The canonical process-tree watchdog enforced 300 seconds and 6,291,456 KiB. The probe completed in 90.865 seconds with peak descendant RSS 4,137,632 KiB and `quiescent=1`; source and executable hashes were unchanged afterward. GDB's exit 0 means evidence collection completed, not that compilation passed.

## Exact fault and causal mapping

The actual worker stopped at `0xaa336c`, `relocate_provider_type+200`, executing `ldr x11, [x10]` with `x10=0xf198715900000000`. Its chain is `relocate_provider_callable -> register_provider_method -> lower_module -> lower_module_transient_scoped -> lower_to_mir_with_target_context`.

At `0xaa5a54`, the caller loads `source.type_` from the HirSymbol field at offset 24 into argument x1; at `0xaa5a60`, it calls `relocate_provider_type`. The declaration is `HirSymbol.type_: HirType?`, while that callee requires `HirType`. The old source checked `source.type_ != nil` but passed the optional field itself without extracting its payload.

The callee copies the argument as the two-field HirType record (`kind`, `span`). The supposed span word is `x19=0xf198715900000001`. This matches the runtime enum layout exactly: `RtCoreEnum` stores enum_id 1 (Option) and discriminant 4053299545 (`SPL_HASH_SOME`, hexadecimal `0xf1987159`) together in its second 8-byte word. The callee is reading a boxed Some wrapper as HirType, then treating that header word as a tagged Span address. Removing the low tag bits produces the faulting address. This mapping comes from the recorded registers/disassembly and `runtime_native.c`'s existing enum layout/constants; it does not depend on guessing a method owner or layout identity.

## Minimal repair

Keep the existing absent-type guard. Within it, extract the slot through the established `source.type_ ?? HirType(kind: HirTypeKind.Error, span: source.span)` contract into a declared HirType local, then pass that payload to `relocate_provider_type`. The fallback is Error, not an invented type; the existing nil path still leaves the target signature absent. Provider ownership, callable privacy, method registration, and the nested-index fix are unchanged. This uses the guarded coalescing pattern already selected for the analogous binding-source-type failure, rather than relying on an unproven native optional binder.

## Regression and next gate

`test/fixtures/compiler/provider_callable_optional_type.spl` is a focused single-module fixture with two local enum methods returning distinct integer/text results. It requires registration/relocation of method signatures before real execution can satisfy its four assertions and `PROVIDER_CALLABLE_OPTIONAL_TYPE_PASS` marker. It is authored but has not been compiled or run with the correction. The original nested-index fixture remains unchanged and is the exact observed crash regression.

Before admission, include this repair with the separately owned source-closure callback repair in the coordinator's changed-source constructor. Then require real ARM execution of the focused and original nested-index fixtures and genuine LLVM 18 RISC-V objects (EM243). Do not treat a GDB capture, source review, old combined-producer PASS, or constructor success as those gates. No new compiler was constructed, no frozen source was edited, and no ordinary task was run with the Rust seed in this lane.

[Evidence receipt](../evidence/native_provider_callable_optional_type_2026-10-11.json) preserves the exact command, environment, source/producer/fixture identities, fault mapping, watchdog receipt, and log hash. Full GDB log and helper are under `/home/yoon/dev/simple-enum-field-owner-20261011/build/native_probe/enum-field-owner/release-cycle2-mir-debug/`.
