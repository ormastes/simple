# Phase4 result owner and window-manager facade exports

Status: source repair; native qualification pending.

The Windows full-CLI cohort at source 9737d1217bc4 reports missing
`compiler.driver.CompileResult` in the external leak runner. The driver module
has no such export; the actual lightweight owner is
`compiler.common.driver_compile_result`. Import that owner directly, matching
the result returned by the existing codegen API.

The same cohort reports three missing deadline APIs in `std.play.wm.mod`.
All eight deadline variants exist in the no-GC synchronous implementation, but
the no-GC asynchronous facade selectively exports only older APIs. Both GC
facades transitively forward that incomplete list. Restore the deadline APIs
to the shared facade without replacing the backend or its timeout behavior.

The four family regression specs call inventory, focus, and target typing with
an already-expired deadline, requiring the actual TIMEOUT error. This checks
public resolution across all families and exercises rejection before process
execution or window side effects. These cases have not yet run; source review
and fixtures are not evidence of native success.
