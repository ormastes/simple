# AOP Log Policy Spec

Source: `test/01_unit/compiler/frontend/aop_log_policy_spec.spl`

## Scenarios

- Classifies hardware and external-access joins as audit logging that remains weaveable in release builds.
- Omits trace and ordinary debug joins from release output unless debug logging is explicitly enabled.
- Keeps compiler AOP debug instrumentation globally disabled by default.
- Enables function-call logging and variable-assignment logging independently.
- Keeps compile-time and runtime log levels separate; compile-time `off` disables both call and assignment instrumentation.
- Builds call-only and assignment-only weaving rules that match MIR `join:call` and `join:assignment` join points.
- Guards the driver pipeline so global log rules are considered before the no-advice skip.

## Reproduction

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/frontend/aop_log_policy_spec.spl --mode=interpreter --no-cover-check
```
