# Native test runner producer lacks source-authority refresh support — 2026-10-21

The explicit native test-runner lane invokes its selected compiler with
`native-build --refresh-source-authority --entry-closure`. In the classifier
runner diagnosis on 2026-10-21, the runner selected the configured `SIMPLE_BINARY`
as intended, but replaying the captured child command with the retained staged
input exited 1 and printed:

```text
Error: unknown option: --refresh-source-authority
```

The selected r17 compiler does not implement the source-authority refresh
capability required by this lane. This is a producer/tool qualification gap; do
not remove the flag or weaken the runner's source-authority requirement to make
that producer appear compatible. Use a producer that supports the option, or
add the capability to the producer before claiming this native lane is
qualified.

The runner previously returned only child stderr on explicit-AOT compile
failure, hiding this error when the child wrote it to stdout. The failure
diagnostic now includes bounded stdout and stderr, exit and limit status, budget
status, and any owned-process completion receipt. This preserves the failure
verdict while making later producer incompatibilities diagnosable.
