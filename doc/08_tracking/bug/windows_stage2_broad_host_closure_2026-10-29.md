# Windows Stage2 broad host facade retains unrelated runtime requirements

Status: narrow owner diagnostic PASS: links without the 75 undefined symbols
and executes CPU, text, stdin and refcount checks. Full Stage2/runner qualification remains pending.

The MSVC Stage2 seed compilation retained 1614 module objects but failed linking
with 75 undefined `rt_*` symbols. Every diagnostic identifies the same archive
member, `libspl_objects.a(mod_1501.o)`, containing `nogc_sync_mut.sffi.host`.
The object has a single `.text` section and no function COMDAT sections. Needed
host queries therefore retain unrelated privileged hardware, TLS, rendering,
storage and database wrappers. This is a closure boundary problem, not evidence
that all 75 providers belong in the bootstrap runtime.

Evidence lives under `.simple/storage/build/bootstrap/`: the full diagnostic is
`logs/x86_64-pc-windows-msvc/stage2-native-build.log`, retained objects are in
`stage3/x86_64-pc-windows-msvc/native-objects-VH5O1D/`, and the original command
transcript is `stage3/x86_64-pc-windows-msvc/stage2-command.transcript`.
The exact symbol report is `build/runner-goal-logs/stage2-link-failure-exact75.md`.
The transcript and debugger inspection confirm no-stub fallback was requested.

`llvm-nm --defined-only` on the frozen native-all, compiler-backfill and runtime
archives found none of the 75 missing symbols, but found all needed CPU query,
refcount, stdin-line and integer-text conversion providers. Existing
`sffi/raw_bytes.spl` documents the same broad-facade closure hazard.

The repair extends the existing narrow CPU owner and extracts refcount and
hosted text owners, preserving signatures and compatibility reexports from
`sffi.host`. Compiler, memory, SOSIX stdin and runner coverage callers import
those leaves directly. No runtime implementations, dummy results or stubs are
added. Preserve the failed module cache and immutable original transcript.

Focused native evidence must compile and execute
`test/fixtures/bootstrap_builder/host_owner_closure_probe.spl` against the
frozen runtime, with no-stub fallback and stdin `owner-probe` plus LF. Inspect
its compiled closure for exclusion of the broad host facade. The probe checks
real CPU queries, negative integer formatting, input and refcount ownership;
it does not qualify the full Stage2 compiler, test runner, or MCP/LSP surfaces.

The first probe compiled four modules and reduced the link failure to
`rt_read_stdin_line`, but selected core-C-only because its entry basename was
`host_owner_closure_probe.spl`. The original Stage2 entry is `bootstrap_main.spl`
with `SIMPLE_BOOTSTRAP=1`: the seed's `is_bootstrap_main_entry` selects native-all
plus a core-C supplement for that lane. Native-all supplies the actual tagged
stdin provider; this is not a missing-provider claim for the original build.
The C `rt_stdin_read_line_text` is not an equivalent substitute: its newline
and long-line behavior differs. Preserve the existing ABI and retry only a
diagnostic fixture with the original lane, separate cache and finite timeout.

The lane-matched diagnostic used an identical copy of the probe named
`bootstrap_main.spl` with `SIMPLE_BOOTSTRAP=1`. It linked four modules in eleven
seconds, exit 0, with no undefined symbols. Artifact SHA256:
`E5FBC605373C118F773FFBC997A747772C9BBD68D2F0508EE06A44C35E99CD01`.
Execution with the harness's stdin input exited 4 at the stdin equality check;
no PASS marker printed. CPU checks and negative integer formatting preceded
that branch, while refcount checks were not reached. The provider source
returns tagged `RuntimeValue` text and strips trailing LF/optional CR; it is
not the raw-pointer C stdin ABI. Exact input injection requires inspection
before assigning the behavior failure to the provider or this owner move.
At that historical stop, the three-cycle budget was exhausted; no further execution or rebuild followed
this diagnostic. Logs and Luna's detailed evidence are retained under
`build/runner-goal-logs/host-owner-bootstrap-lane-build.log` and
`build/runner-goal-logs/host-owner-probe-evidence.md`.

The repository-wide SFFI audit stopped at its existing aggregate ceilings:
`source_variants=409/399 migration=3737/3546`. A targeted `git show HEAD`
comparison of the old host/CPU owners with the four current owners found an
identical multiset of 326 extern-declaration and unsafe-annotation lines. No new
foreign symbol, ABI signature or missing unsafe annotation is introduced by
this move. This scoped comparison is not a claimed passing full-tree audit.
# Corrected stdin evidence (2026-10-30)

The earlier PowerShell `StandardInput.BaseStream` attempt supplied a buffer of
12 bytes, `6f776e65722d70726f62650a`, but that did not prove the child pipe was
BOM-free. A diagnostic executable printing its input showed an actual leading
U+FEFF: `received=<\uFEFFowner-probe>`. Its negative-integer text control printed
`known-tagged-text=<-42>` correctly. The PowerShell input harness introduced the
BOM; no provider, comparison, or return-ABI repair was needed.

After the user authorized continued diagnosis, Python subprocess raw PIPE input
sent those same 12 bytes to the ORIGINAL retained executable, SHA256
`E5FBC605373C118F773FFBC997A747772C9BBD68D2F0508EE06A44C35E99CD01`.
It exited 0 and printed `narrow host owners: CPU, text, stdin and refcount PASS`
with empty stderr. No rebuild was needed for this successful run. Evidence:
`build/runner-goal-logs/host-owner-bootstrap-lane-stdin-rawpipe.txt`.
The distinguishing value-echo evidence is
`build/runner-goal-logs/host-owner-stdin-value-build-run.log`.

Preserve the earlier exit-4 logs as harness-failure history. Their `no BOM`
label describes the supplied buffer, not validated bytes at the child pipe,
and is superseded by the raw-pipe evidence. The earlier retry-budget stop was
historical; the user's later continuation authorized this diagnosis.

This is a focused native-owner PASS only. The full Stage2 compiler, requested
runner matrix and MCP/LSP surfaces still require their own qualification.