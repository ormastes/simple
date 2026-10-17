# A174 named enum payload owner loss (2026-10-16)

Status: bug database reconciliation pending; source workaround, native qualification pending.

Producer SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994 reports 26 errors at thirteen HirType.named payload constructors: undefined HirTypeKind and unresolved Int/Float. Evidence: phase3-validation-20261016/authority-attempt3-failures.json. Bool/Unit constructors have no payload and no corresponding retained errors.

Retained producer source windows-diagnostic-parent-20261012/source/src/compiler/20.hir/hir_lowering/_Expressions/declared_enum_constructor.spl, declared_enum_constructor_expr, explicitly returns nil when any argument has_name. Its positional path retains the declaring owner in HirTypeKind.Named and constructs HirExprKind.EnumLit. The newer source supports validated declaration-order named arguments; changing that source does not change the retained executable. This is evidence for a named-argument route difference, not imported method-body cloning.

Workaround changes only thirteen calls in HirType.named to positional arguments. HirTypeKind declares Int(bits: i64, signed: bool) and Float(bits: i64); the original calls already use precisely that order. All names, widths, signedness, usize/isize 64-bit mappings, bool/unit branches, and unknown-name signed64 fallback remain identical. No representation, enum ID, default, metadata, or module is removed.

Recovery baseline: 496b77c9827, before the workaround. Compiler owner: HIR declared enum constructor lowering. Restore named calls only after a rebuilt producer verifies them. Actual workaround commit is recorded in the follow-up evidence. No fourth authority or focused retry is authorized. Qualification belongs to the remaining full Phase3 cycle; source reasoning is not runtime PASS. Separate decoder payload type mismatches remain unresolved by this patch.
