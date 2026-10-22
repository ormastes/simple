# Windows asynchronous children lose standard streams

The core-C `rt_process_spawn_async_owned_windows` owner used
`CREATE_NO_WINDOW` without explicitly assigning its standard handles. Native
HIR shard children could exit 1 while the coordinator retained only their
exit status, losing the early diagnostic. The original full CLI attempt
selected 2229 modules, parsed successfully, then four HIR children failed
before publishing any inventory. Their actual refusal remains unknown;
this fix restores diagnostic transport rather than claiming to repair it.

The owner now duplicates stdin, stdout and stderr using the existing runtime
handle helper, publishes those three handles through STARTUPINFOEX and an
explicit inheritance list, and closes its duplicates after launch. Missing
GUI-parent streams use NUL. Duplication or setup failures refuse the launch.
PID registration and wait ownership remain unchanged.

The genuine core-C Windows selfcheck uses non-inheritable parent pipes,
requires the child to read stdin, verifies distinct stdout/stderr and exit 23,
and checks that an unrelated inheritable event is excluded. It also checks
absent GUI streams, a timeout followed by a successful reap, double wait,
and missing executable failure. No runtime exports are replaced by mocks.

Native counterfactual executed once with pinned clang-cl and static /MT:
the original runtime archive failed the test with exit 5; the patched
runtime process object passed with exit 0, exact
`WINDOWS_ASYNC_STDIO_PASS` plus LF, and empty stderr. Link maps bind the
actual function to the original runtime_process.obj and patched fixed.obj
respectively. A receipt observer initially expected CRLF; its assertion was
reconciled from retained bytes without rerunning the test.

Local evidence:
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/windows-async-stdio-PENDING/counterfactual-terminal.json`
and the adjacent compile/link/run receipts, maps, input pins and guard receipt.
This qualifies Windows C process stream behavior only. Whole compiler, full
CLI and whole test suite qualification remain pending. Bug DB reconciliation
is pending availability of a qualified full CLI.
