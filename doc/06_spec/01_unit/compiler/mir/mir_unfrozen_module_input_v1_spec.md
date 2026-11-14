# Unfrozen target-bound MIR entry

Source: `test/01_unit/compiler/mir/mir_unfrozen_module_input_v1_spec.spl`.
Status: all seven scenarios **UNEXECUTED**. This manual was authored alongside the specification; doc generation, native compiler checks and runtime scenarios have not run.

| Scenario | Observable assertion |
|---|---|
| Mismatched profile | Named mismatch before module marker, return-type table, capture rows or diagnostics change |
| Unresolved carrier | Trimmed/case-insensitive placeholders in arch, OS, ABI or backend rejected by packaging and again at strict entry, including direct struct construction |
| Native backend | Common normalizer retains native, and the bound entry lowers its actual module |
| None ABI | Common normalizer’s SimpleOS context packages with its valid none ABI |
| Profile selection | Actual MIR from two guarded declarations contains exactly the function enabled by debug/release context |
| Session reuse | Same-target calls admitted; changing both mutable target and requested input after lowering rejects with named rebound error and preserves recorded scratch |
| Verification routes | Explicit target gives closed direct-call manifests and repeatable receipts; legacy unknown-context producer remains usable; explicit unknown-context producer rejects |

The fixtures parse source into HIR and use the actual MIR lowerer. Profile guards are attached to semantic declarations to test MIR selection independently of parser preprocessing. No fake frozen snapshot, fabricated MIR or synthetic resolver receipt is used. Scratch assertions sample observable state; source review establishes that guard execution precedes entry into trace/cfg lowering. They are not a full mutation or native-memory proof.

Static transient-boundary gate: the initial parent failed on existing missing MirBuilder writeback roots and public SFFI parsing. After repair PR #9223 and rebase onto `1a90b730`, a single gate run passed 35 scanner fixtures and 18 production invariants, including the new constructor binding root. The seven behavioral scenarios remain UNEXECUTED; static PASS does not replace native lifetime or feature verification.
