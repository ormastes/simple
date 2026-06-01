# Feature: aop-log-debug

## Raw Request
$sp_dev  improve log with aop and skill of spipe >> aop to on/off global log func call and variable assign for debugging(most case no overhead in compile time).  update debug skill on spipe to not edit for log use aop for log codes and not delete added log call (which can not handled by aop log) but change log level when it is no longer needed.
Specify compile/runtime log level. debug level is default compile time log level. however can change compile time log level during compile.
(let log is default rather print, allow print on script without warning) print on none script code to warning to change it to log().  update bare metal.

## Task Type
feature

## Refined Goal
Add compiler-controlled AOP debug logging for function calls and variable assignments, make log-level policy explicit across compile time, runtime, SPipe debug guidance, print diagnostics, and bare-metal logging.

## Acceptance Criteria
- AC-1: Compiler AOP logging can be globally enabled and disabled for function-call logging, with disabled/default paths imposing no per-join-point compile-time work beyond reading the effective disabled policy.
- AC-2: Compiler AOP logging can be globally enabled and disabled for variable-assignment logging, with disabled/default paths imposing no per-assignment instrumentation.
- AC-3: Compile-time and runtime log levels are specified separately; compile-time defaults to debug and can be changed during compile.
- AC-4: The SPipe debug skill tells agents to use AOP logging for removable debug instrumentation instead of editing source with ad hoc log calls.
- AC-5: The SPipe debug skill tells agents not to delete manually added log calls that AOP cannot cover; when they are no longer needed, agents must lower the log level instead.
- AC-6: `log()` is the preferred default diagnostic output API over `print()` for non-script code.
- AC-7: `print()` remains allowed in scripts without warning.
- AC-8: `print()` in non-script code produces a warning recommending `log()`.
- AC-9: Bare-metal logging documents and exposes the compile/runtime log-level policy without requiring hosted runtime services.

## Scope Exclusions
- Converting every existing print call in the repository is out of scope for the first implementation slice.
- Release/tag/push is out of scope until verification proves the full objective.

## Phase
dev-done

## Log
- dev: Created state file with 9 acceptance criteria (type: feature).
- impl: Added AOP log instrumentation policy helpers for function-call and variable-assignment toggles plus separate compile/runtime levels.
- impl: Added SPipe debug guidance to prefer AOP logging for removable debug traces and lower manual log levels instead of deleting non-AOP log calls.
- impl: Added bare-metal log policy helpers with explicit compile/runtime levels and no hosted runtime dependency.
- impl: Added parser warning path for bare `print` in non-script code; focused parser spec could not be retained because the current release test runner cannot resolve the parser entrypoint exports in existing parser specs.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --no-cover-check` passed.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/system/os/baremetal/feature/log_policy_spec.spl --mode=interpreter --no-cover-check` passed.
- impl: Extended AOP core with `FunctionCall` and `VariableAssignment` join-point kinds, `join:call` / `join:assignment` predicates, and advice call block/instruction metadata.
- impl: Added policy-built weaving rules for compiler AOP log calls and assignments, and wired driver env knobs `SIMPLE_AOP_LOG_CALLS`, `SIMPLE_AOP_LOG_ASSIGNMENTS`, `SIMPLE_AOP_COMPILE_LOG_LEVEL`, and `SIMPLE_AOP_RUNTIME_LOG_LEVEL`.
- impl: Updated MIR AOP insertion so call logging inserts before the matched instruction and assignment logging inserts after the matched instruction.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/frontend/aop_weaving_config_spec.spl --mode=interpreter --no-cover-check` passed after fixing `core/aop.spl` parser-incompatible `context:` named constructor arguments.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --no-cover-check` passed with 10 examples, including call-only and assignment-only MIR join-point matches.
- verify: `test/unit/compiler/mir/aop_injection_spec.spl` remains blocked in this runner by an existing `MirTerminator.Return` enum parser incompatibility in `src/compiler/50.mir/mir_instructions.spl`; call/assignment AOP behavior is covered through the frontend AOP policy spec instead.
- impl: Renamed the MIR terminator variant from keyword-conflicting `Return` to parser-safe `Ret` across MIR/backend users, renamed SIMD enum payloads that used `val`, and rewrote constant-folding `return nil` expression arms into statement form so `mir_instructions.spl` can parse further under the release runner.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --no-cover-check` passed again with 10 examples after the MIR parser fixes.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/frontend/aop_weaving_config_spec.spl --mode=interpreter --no-cover-check` passed again with 16 examples.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/system/os/baremetal/feature/log_policy_spec.spl --mode=interpreter --no-cover-check` passed again with 3 examples.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- verify: `test/unit/compiler/mir/aop_injection_spec.spl` now gets past the MIR terminator keyword blocker but remains blocked by an existing parse issue in `src/compiler/30.types/type_layout_part2.spl` (`Unexpected token: expected expression, found Newline`).
- impl: Normalized parser-incompatible compact forms in `src/compiler/30.types/type_layout_part2.spl` that blocked the MIR AOP injection spec import path.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple src/compiler/30.types/type_layout_part2.spl` completed successfully after the syntax normalization.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/mir/aop_injection_spec.spl --mode=interpreter --no-cover-check` passed with 6 examples.
- verify: Focused regression specs passed again: AOP log policy (10 examples), AOP weaving config (16 examples), and bare-metal log policy (3 examples).
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0` after focused verification.
- verify: Required broad smoke checks (`simple check src/compiler`, `src/lib`, `src/app/mcp`, `src/app/simple_lsp_mcp`) are still blocked by unrelated parser debt in the wider driver/frontend import graph; after small local normalizations they now stop at `src/compiler/10.frontend/flat_ast_bridge_part2.spl` (`expected expression, found Else`).
- verify: Required MCP stdio integration smoke was attempted and failed on existing import-graph parse/semantic blockers (`compiler/tools/fix`, `app/io/cli_compile_part*`, `std/common/spec/scenario_helpers`, and missing `proc_slot_acquire`), not on the focused AOP logging specs.
- impl: Cleared several narrow parser-compatibility blockers in the required compiler smoke import path: `flat_ast_bridge_part2.spl`, HIR lowering item parts, common effects tags, bitfield layout naming, and MIR contract compact matches.
- verify: Focused AOP/bare-metal regression specs passed after those parser fixes: AOP log policy (10 examples), AOP weaving config (16 examples), MIR AOP injection (6 examples), and bare-metal log policy (3 examples).
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- verify: `bin/release/x86_64-unknown-linux-gnu/simple check src/compiler` now advances past the earlier blockers and stops at a new unrelated compact-match parse issue in `src/compiler/50.mir/mir_effects.spl` (`expected newline after match, found Case`).
