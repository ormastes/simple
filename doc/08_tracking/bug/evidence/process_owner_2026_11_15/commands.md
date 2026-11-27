# Native physical-boundary evidence

Each compile and execution used `systemd-run --user --scope --quiet -p MemoryMax=512M -p MemorySwapMax=0 timeout --signal=KILL 30s` followed by the command below. Separate logs preserve all six exits. The initial 30GiB disk preflight stopped before compilation; root authorized a small-C-fixture exception with 1GiB minimum disk and 16MiB total outputs. The successful preflight is retained.

```
cc -Wall -Wextra -Werror -I src/runtime -o PRIVATE/owned-child src/runtime/test/process_owned_child_selfcheck.c src/runtime/runtime_process_tree.c
PRIVATE/owned-child
cc -Wall -Wextra -Werror -I src/runtime -Wl,--wrap=getsid -Wl,--wrap=readdir -o PRIVATE/enum-red src/runtime/test/process_enumeration_failure_selfcheck.c PRIVATE/old-runtime-process-tree.c
PRIVATE/enum-red
cc -Wall -Wextra -Werror -I src/runtime -Wl,--wrap=getsid -Wl,--wrap=readdir -o PRIVATE/enum-green src/runtime/test/process_enumeration_failure_selfcheck.c src/runtime/runtime_process_tree.c
PRIVATE/enum-green
```

`PRIVATE` was `/tmp/directory-process-native-20261115`. Old source was extracted from `6ff8d46ef32:src/runtime/runtime_process_tree.c`; its bytes were verified identical to release base `f7e30f9e751`. The current source hashes are retained separately. Owned-child checks use real fork/pipe/wait operations. Enumeration fault injection wraps only getsid/readdir; the production enumerator and signal-zero path are unchanged code. This proves Linux physical-boundary behavior, not a whole runtime, compiler, or directory scheduler execution. macOS error handling was source-reviewed only; FreeBSD and unsupported hosts were not executed.
