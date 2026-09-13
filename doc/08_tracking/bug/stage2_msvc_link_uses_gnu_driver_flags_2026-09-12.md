# Stage 2 link passes GNU driver flags to cl.exe (Windows/MSVC)

- **Status:** OPEN
- **Severity:** P1 — blocks Stage 2 of the Windows/MSVC bootstrap
- **Discovered:** 2026-09-12
- **Lane:** `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload`

## Symptom

Stage 2 now compiles and archives the core-c-bootstrap runtime supplement
successfully, then fails at the final link:

```
cl : command line warning D9035 : 'o' option is deprecated ...
cl : command line error D8021 : invalid numeric argument
      '/Wl,/INCLUDE:__module_init_app__build__targets__action_identity'
Build failed: link failed: Microsoft (R) C/C++ Optimizing Compiler 19.44.35228 (x64)
```

## Cause

The link step drives `cl.exe` with GNU **driver** syntax:

- `-Wl,<arg>` — the GCC/Clang spelling for "pass this to the linker". MSVC's
  driver has no `-Wl,`; the correct spelling is `/link <arg>` (everything after
  `/link` goes to `link.exe`), so cl parses `-Wl,...` as the `/W` warning-level
  option and rejects the rest as a bad numeric argument (D8021).
- `-o <exe>` — cl reads this as its deprecated `/o` (D9035) rather than as the
  output path; the MSVC spelling is `/Fe<path>`.

This is the *link* counterpart of the compile-side defect fixed by PRs #573 and
#577, which mapped the GNU **compile** flags (`-o` -> `-Fo`, `-Os` -> `-O1`,
`-ffunction-sections` -> `-Gy`, `-fdata-sections` -> `-Gw`,
`-fno-stack-protector` -> `-GS-`) in
`build_c_runtime_library` / `build_sqlite_runtime_object`
(`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`). The link
invocation was not covered by those changes.

## Evidence that the earlier layers are now fixed

Same lane, successive runs:

| stage | before | after |
|---|---|---|
| C supplement compile | 10 `C2065` undeclared identifiers | compiles clean |
| archive | `llvm-ar: runtime_native.obj: no such file or directory` | archive produced |
| link | not reached | `D8021` on `-Wl,` (this bug) |

`D9035`/`D9002` occurrences in the stage2 log fell from 214 to 8, the remainder
all originating in this one link invocation.

## Fix direction

Give the link step the same compiler-conditional treatment the compile step now
has — branch on
`simple_common::platform::cc_detect::is_msvc_compiler`, emit `/Fe<path>` for the
output and `/link /INCLUDE:<symbol>` for the forced-reference arguments, and
leave the GNU branch byte-identical. The `/INCLUDE:` payloads themselves are
already MSVC-correct; only the driver wrapper around them is wrong.

## Not yet investigated

Three further compile sites still pass GNU `-o` and have no MSVC branch —
`compile_inline_asm_c` (`inline_asm_emit.rs`), `generate_stub_object_freestanding`
(`stubs.rs`) and the boot-assembly loop in `linker.rs`. All three are
freestanding/`--target=` cross lanes and were NOT reached by this hosted
Windows bootstrap, so whether they can ever receive `cl.exe` is unverified and
is deliberately recorded here as an open question rather than asserted.
