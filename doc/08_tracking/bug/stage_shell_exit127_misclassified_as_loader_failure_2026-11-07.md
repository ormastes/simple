# Shell exit 127 misreported as a Windows loader entrypoint failure

Severity: P2. Status: fix implemented; focused caller regression verified, landing pending.

During the bounded provisional Phase3 build, the native compiler lowered 464 of 1,601 modules before a 900-second worker timeout. The shell reported exit 127; `stage-exe-launch.shs` incorrectly diagnosed STATUS_ENTRYPOINT_NOT_FOUND and an LLVM DLL clash from that shell status alone. A running program's exit 127 is ambiguous and is not a native NTSTATUS receipt.

The launcher now reports shell 127 as ambiguous and directs diagnosis to actual output and the native process/timeout receipt. Signed and unsigned STATUS_DLL_NOT_FOUND and STATUS_ENTRYPOINT_NOT_FOUND retain their specific diagnostics. Arguments, output and child exit status are preserved; missing executable behavior is unchanged.

The actual private caller regression passed 10/10 cases (`build/review/stage-launch-exit127-fix/evidence.sdn`). The new process fixture prints `lowered 464 modules`, exits 127, and asserts retained stdout/status without an entrypoint-failure claim. Four signed/unsigned NTSTATUS classification controls remain. A later comment-only clarification did not change executable logic; unchanged green checks are not replayed for landing.

This change corrects diagnostic attribution. It does not fix the underlying Phase3 worker timeout, reproduce a fresh native loader failure, qualify a compiler generation, or establish release/MCP admission. No compiler/runtime source changes are included.