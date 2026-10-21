# Dotted external native entry identity

Source: `test/01_unit/compiler/driver/dotted_source_entry_identity_spec.spl`.
Status: hand-authored source-only expectations; every scenario is UNRUN. This is
not generated execution evidence and carries no production verification claim.

The compiler team uses these scenarios to check the alias name consumed by
lowering against the real LLVM entry-name derivation and entry-selection predicate.

| Scenario | Expected result | Requirement |
|---|---|---|
| Entry `/tmp/simple_dotted_entry/dot.1/hello.spl` | Primary alias `.tmp.simple_dotted_entry.dot.1.hello`, matching native entry derivation | REQ-DOTTED-ENTRY-001 |
| Entry under `g.1/sub` | Preserve `g.1` in the primary name | REQ-DOTTED-ENTRY-001 |
| Same basename under `dot.1` and `dot.2` | Distinct primary identities; neighbor must not match selected entry | REQ-DOTTED-ENTRY-002 |
| `nodot1`, `a-b`, and `dot.alpha` controls | Retain shared derivation, including established punctuation sanitization | REQ-DOTTED-ENTRY-003 |
| Existing repository `src/compiler/10.frontend/core/lexer.spl` spelling | Keep canonical `compiler.frontend.core` alias first | REQ-DOTTED-ENTRY-003 |
| Production LLVM predicate with `SIMPLE_NATIVE_BUILD_ENTRY` set | Requested dotted alias is entry; neighboring dotted alias is not entry | REQ-DOTTED-ENTRY-001/002 |
| Relative and absolute external paths with `hello.1.spl` | Each primary alias matches LLVM derivation for the same spelling; `hello.2` differs | REQ-DOTTED-ENTRY-001/002 |
| Filename `hello.spl.spl` | Remove only final `.spl`; retain inner `.spl` in identity | REQ-DOTTED-ENTRY-001 |

Additional root-membership scenarios close independent review finding DOT-PATH-01:

| Scenario | Expected result | Requirement |
|---|---|---|
| Real external files under a secure temporary directory's `src/dot.1` and `src/dot.2` | Preserve shared names `dot.1.hello` and `dot.2.hello`; LLVM selects only `dot.1` | REQ-DOTTED-ENTRY-004/001/002 |
| Real external files under its `examples/dot.1` and `examples/dot.2` | Preserve distinct shared `examples.*` names; LLVM selects only the requested entry | REQ-DOTTED-ENTRY-004/001/002 |
| Actual repository lexer file reached relatively and absolutely with a historical numeric-tier alias | Physical root proof admits canonical `compiler.frontend.core.lexer` first in both forms | REQ-DOTTED-ENTRY-004/003 |
| Actual repository `examples/01_getting_started/hello_native.spl` reached relatively and absolutely | Both forms retain `examples.01_getting_started.hello_native` | REQ-DOTTED-ENTRY-004/003 |

The spec temporarily sets entry-closure and selected-entry environment values and
restores each previous value before assertions. It calls production APIs; it does
not replace or emulate compiler behavior. No compiler process, linker, binary, or
compiler binary needs to be manufactured for these owner/API assertions.
The new external-membership scenario authors real files only when this UNRUN
spec is eventually executed; it uses the existing secure-temp, directory, and
file APIs and removes the temporary tree afterward. No compiler substitutes or
new test toolchain are introduced.

A future qualified producer must also compile and run the report's hello-world
entries in `nodot1`, `a-b`, `dot.1`, and `g.1/sub`; require actual link success,
`__simple_main`, stdout `hi`, and exit zero, and reject a neighboring main becoming
the selected entry. All runtime/link checks remain UNRUN in this packet.
The stage-binary gate workaround must remain until that evidence exists.
