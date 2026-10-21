# GDB MI transport and DAP condition forwarding

Source-authored scenario manual; execution and generated-manual qualification
are **UNRUN**. Executable specification:
`test/03_system/app/debug/remote/protocol/gdb_mi_transport_spec.spl`.

Canonical assignment 09–12 (DS6 GDB pipes and rich breakpoints) is only
partially addressed by this slice. GDB DAP conditions now use the existing
pipe client. Hit-condition expressions and log-message semantics remain open;
the adapter continues to ignore those two options for compatibility. No
full-rich-breakpoint completion is claimed.

1. Encode one MI C-string argument, preserving spaces, quotes, backslashes,
   newline, carriage return and tab as data. Decode exactly one escape layer,
   retaining literal C escape sequences. Validate wrapped breakpoint result
   tuples and reject missing or invalid breakpoint numbers before caching.
2. Create a disconnected adapter. Basic and conditional breakpoint requests
   must return `GDB client not connected`. Unknown architecture must fail
   before spawning GDB.
3. Start real GDB over the existing piped-process facade, load a compiled
   fixture, set a backend conditional breakpoint and inspect its cached model.
4. Transfer ownership of that live client to the DAP adapter. Request a
   conditional breakpoint at a source filename containing spaces with quotes,
   backslashes, literal C escapes and a physical newline in the condition. Inspect the adapter's
   cached condition, line and next command token.
5. Request None, empty-condition and basic breakpoints sequentially. Assert
   increasing IDs and persistent cache entries, including the original rich
   condition.
6. Submit an invalid expression, require GDB's error, then submit another valid
   basic request. Assert token progression and exactly six cached successful
   breakpoints; the failed command must not create a cache entry.
7. Disconnect through the owning adapter. Exercise the actual configuration
   bridge with a nonexistent program and require a propagated GDB error.
   Use the explicit x86_64 architecture so host GDB is sufficient.

The real-process scenario reports its existing dependency skips explicitly:
GDB, GCC or registered piped-process externs may be absent. A skipped scenario
is not runtime evidence for condition transport. Missing/failed Simple probe
runners fail rather than silently skip.
Fixture compilation failure also fails the scenario after GCC is available.

The bridge maps canonical architecture names to `DebugConfig.target` and
passes its existing `options` field. `AdapterConfig.timeout_ms` is not
consumed by the pipe client: its startup and result deadlines remain fixed.
Startup symbol-load and remote-connect errors close the just-created process.
Other adapter methods retain their existing receiver/state behavior; this is
not a global ownership repair. Native, runtime, shutdown and startup-leak
qualification remain pending an admitted runner.
