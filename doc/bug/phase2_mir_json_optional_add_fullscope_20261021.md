# Phase2 MIR JSON optional Add failure: candidate and evidence

The frozen `0bfa8039acd` Windows Phase2 attempt ended with 1,431 compiled,
zero reused, and five failed modules. Its `mir_json.spl` failure was
`cannot apply Add to an optional value that has not been unwrapped`.
The primary retained log is the campaign's
`.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`.

The candidate explicitly unwraps the two hexadecimal nibble slices in
`escape_json_string`. Its enclosing guard restricts the input code to 0..31;
both single-byte slices therefore lie within the 16-byte hexadecimal alphabet.
No fallback value, assertion suppression, unsupported grammar workaround, or
compiler admission bypass is introduced. This is a scoped source candidate;
the full-project failure has not yet been shown to disappear.

## Exact producer and observations

Focused bootstrap diagnostics used the campaign's frozen seed at
`stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe` under the
canonical sourced Windows MSVC environment. SHA256:
`32014b3401e3cb76aec44acb475a22f2385fefcd1d19ab71049e52d633356825`.
`SIMPLE_BOOTSTRAP=1` and `SIMPLE_NATIVE_BUILD_RUST=1` identify these as bootstrap
diagnostics, not product tests or self-hosted evidence. All source/cache writes
were confined to the private checkout `D:/dev/simple-http-client-imports-20261021`.

Counterevidence matters: both original and changed `mir_json.spl` compile in
the 127-module archive closure. The changed closure built 127 modules with no
failures; the original source retry built one and reused 126 with no failures.
An extracted original escape function also compiles. Thus the error depends
on the full project's injected import/type context; isolated acceptance does
not prove a causal repair. No global import-map repair is claimed here.

The supported seed command for the owner was:

```text
native-build --source src/compiler/50.mir/mir_json.spl
  --entry src/compiler/50.mir/mir_json.spl --backend llvm --threads 1
  --emit-archive --cache-dir build/mir-json-option/owner-cache
  -o build/mir-json-option/owner.lib
```

The runtime diagnostic extracted the exact changed production function and
the body of `test/04_smoke/mir_json_control_escape_native_probe.spl` into a
tiny private Git checkout. With `SIMPLE_NO_STUB_FALLBACK=1`, the same seed
compiled that fixture to a real PE executable, which then reported:

```text
MIR JSON escaping: 36 checks, 0 failures
```

The checks cover every control byte 0..31 against explicit expected escapes,
quote/backslash escaping, empty input, non-ASCII text, and ordinary slashes.
The native character provider constructs inputs independently of the escape
algorithm. This proves the extracted implementation's runtime behavior; the
checked-in fixture importing the actual MIR owner and the full-project retry
still need execution in their real contexts.

Private evidence is under `build/mir-json-option/`: `owner.log`,
`owner-baseline.log`, and `fixed-runtime-abi.log`, plus retained fixture Git
snapshots and caches. Early diagnostic use of unsupported `--emit-object`
produced PE executables named `.o`; those are not native object receipts.

## Required closure

Retry the actual full source inventory with the exact producer and compatible
cache, collecting all failures. Only that retry can establish whether the
candidate clears this original Phase2 boundary. The produced compiler must
then compile Hello and execute its output before dependent provisional Phase3.
