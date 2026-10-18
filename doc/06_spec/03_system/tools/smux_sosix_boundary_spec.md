# SMUX synchronous SOSIX host boundary

Manual companion for `test/03_system/tools/smux_sosix_boundary_spec.spl`.
Authored source controls; not generated or executed with an admitted runner yet.

1. Attempt direct stdin ABI, ordinary host imports, async SOSIX imports and
   direct printing. Each negative control must fail the architecture predicate.
   An empty/missing source file must also fail.
2. Admit synchronous SOSIX aliases and the existing TCP facade. TCP already
   delegates to the synchronous SOSIX network boundary and owns its lifetimes.
3. Inspect the actual smux product entrypoints and both independent Windows
   client fixtures. Every selected source must satisfy the same predicate.

The predicate is a focused source guard, not an import resolver or native
behavior test. It cannot certify linked provider identity, resource cleanup,
console restoration, clipboard behavior or compiler aggregate correctness.

Native control: compile `test/fixtures/compiler_entrypoint/smux_sosix_host/main.spl`
using an admitted producer, pass its existing executable path as its sole
argument, pipe UTF8 `SOSIX_STDIN_λ` plus LF and then close stdin. Under a ten-second
external process-tree watchdog, require exit 0 and exact stdout
`sosix-host-boundary-ok` plus newline. This checks argument normalization,
file existence, stable positive PID, realtime, an actual native 25ms sleep,
monotonic elapsed time, tagged-text Unicode stdin and empty-text EOF.

Then run both independent Windows smux fixtures against the separately built
product using the explicit Windows overlay. Their existing real child I/O,
client separation, resize and teardown checks remain the product evidence.
