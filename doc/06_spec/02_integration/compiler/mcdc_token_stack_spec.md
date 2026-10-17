# MC/DC token stack ownership

Executable specification: `test/02_integration/compiler/mcdc_token_stack_spec.spl`.
Behavioral helpers and direct native entry: `test/02_integration/compiler/mcdc_required_token_probe.spl`.

| Requirement | Executable behavior | Expected result |
| --- | --- | --- |
| REQ-MCDC-TOKEN-STACK-001 | Parse and lower a nested conditional; reuse the same lowerer for following functions and an excluded runtime module. | Two distinct begin tokens close in reverse order; completed stack is empty; following/excluded functions contain no probe calls; actual MIR verifier accepts. |
| REQ-MCDC-TOKEN-STACK-002 | Lower a real HIR Return in an explicitly prepared two-token active MIR context. | Exactly two abort calls use inner then outer token; one return terminator; actual MIR verifier accepts. |
| REQ-MCDC-ENTRY-CONFIGURATION-003 | Parse and lower entry and nonentry main functions in off, static and dynamic modes. | Only enabled entry main configures its selected recorder, exactly once before the first decision; actual MIR verifier accepts. |

The two token-stack checks run in static and dynamic modes; the entry-configuration check also covers off mode. The direct-context return case deliberately isolates MIR cleanup ordering from frontend syntax. The existing native module-statics fixture separately requires real configured MC/DC recording and initialized/shared global values.

Status: authored, UNRUN. Use an actually admitted pure compiled test host to run the SSpec with `--assert-ran`; the bootstrap-only CLI is not such a host, and the Rust seed is bootstrap-only. Native diagnostic execution and SSpec/docgen qualification are separate evidence. The prior full-host attempt hit the 8 GiB cap during HIR, so this manual makes no broad host or core-suite PASS claim. Do not treat copied-source fixture execution as proof of the original excluded `/test/` collection route.

Final bounded evidence (2026-10-16): the small Cranelift storage/positive-recording fixture and LLVM planner startup passed. The larger native compiler-behavior probe completed HIR/monomorphization but stopped during MIR64/413 with semantic failures and RSS exit88; none of its assertions executed. This SSpec and generated docgen remain UNRUN. The supervisor and separate terminal assessment in `.simple/storage/build/phase3-mcdc-initializer-export-20261015/` preserve the distinction. These documentation updates postdate the frozen producer snapshots.
