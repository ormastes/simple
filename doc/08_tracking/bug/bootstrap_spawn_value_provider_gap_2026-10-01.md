# Bootstrap process spawn value ABI gap

Status: source correction; canonical Phase2 admission remains pending.

Frozen source `bf28063b843526d1212a760deaed623367a569e5` lowered all
1089 Linux Phase2 modules but could not link `rt_process_spawn_async_value`.
The linked `libsimple_runtime.a` is the Rust static library: its raw export is
`rt_process_spawn_async(ptr, len, RuntimeValue)`. It does not compile the C
`runtime_native.c` value adapter. The C raw owner has a different contract,
`rt_process_spawn_async(char*, char**, count)`.

The shard launcher also reaches `io_runtime.spl`, which still declared a
semantic two-argument call against the raw name. Windows Phase2 linked but
its first HIR worker failed before claiming work. The caller is corrected;
canonical admission must establish whether any further Windows defect remains.

## Correction

The Rust runtime now exports a separate two-word value adapter, registers it
in seed ABI metadata, ELF resolution, and interpreter dispatch, and retains
the raw three-word export. Native `io_runtime` uses the value name, matching
`process_ops`. The new name is deliberately absent from ptr/len expansion.

Tagged Rust command strings use their explicit byte length; they are not
assumed NUL-terminated. Raw native pointers retain the existing unsafe
NUL-terminated text precondition. Registered non-string heap commands and
non-array argv are refused. Existing nil-as-empty-array behavior is preserved.
Child creation and registry ownership remain with the existing raw owner.

## Focused evidence

`scripts/check/check-process-spawn-value-abi.shs` compiles and links a real
child-process probe against core-C providers, or an explicitly supplied Rust
archive. It verifies tagged/raw command text, a short text command, exact
space/quote/empty argv boundaries, exit37 from the child, and missing-program
failure. Rust-only checks cover registered non-string command, non-array argv,
and non-text argv. The driver requires `--parent`; an accidental empty-argv
spawn exits99 and cannot recursively start the suite.

The Linux core-C round trip passed before the final driver safety guard;
that guard does not alter adapter behavior. Rust provider build, Windows
native harness, and corrected canonical bootstrap are separate pending gates.
These C/Rust ABI probes do not establish a self-hosted Simple test-suite PASS.

Rust unit `async_spawn_value_rejects_invalid_values` uses an existing host
executable so malformed-value refusal cannot be masked by ENOENT. Native
fixtures remain outside `doc/06_spec`.
