# Simple Interpreter DebugServiceV1 Vertical Slice

This executable system specification proves the first REQ-015 vertical slice.
It adapts the existing `app.debug.interpreter_backend.InterpreterBackend`; it
does not add an interpreter, evaluator, breakpoint registry, or execution
transport.

The scenarios require a readable Simple source fixture, bind its SHA-256 digest
to one central `DebugSessionId`, attach the landed runtime hooks, execute the
fixture, create a semantic breakpoint carrying `SourceAnchor + SymbolId`, and
inspect build-bound receipts. Expression evaluation accepts only the existing
backend's local-name lookup shape and rejects calls, assignments, and operators
before dispatch. Tasks, actors, and queues remain visibly `Blocked` because the
existing backend exposes no such inspection API.

Executable source:
`test/03_system/app/debug/feature/simple_interpreter_debug_service_spec.spl`.

Run with:

```text
bin/simple test test/03_system/app/debug/feature/simple_interpreter_debug_service_spec.spl --mode=interpreter
```
