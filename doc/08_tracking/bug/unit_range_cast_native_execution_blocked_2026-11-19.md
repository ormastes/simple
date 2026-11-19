# Unit range-cast / remainder checks: native execution blocked (2026-11-19)

Status: verification-pending. Native machine-code verification NOT achieved.

Fixtures: `test/fixtures/unit_native/{port_oor,port_in,big_reject,big_accept,div_zero}.spl`.

## Lane 1: Rust seed native-build (works, but does not exercise the pure-Simple MIR checks)
Env: llvm-mingw UCRT on PATH (`~/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin`), `SIMPLE_NATIVE_BUILD_RUST=1`.
(`CC=clang-cl` compiles but fails to link: missing libclang_rt.builtins.a / liblibcmt.a / liboldnames.a.)

    SIMPLE_NATIVE_BUILD_RUST=1 C:/dev/simple/bin/simple.exe native-build test/fixtures/unit_native/<case>.spl -o build_rbnat2/<case>.exe

Observed (all five link, rc=0):

| case | exit | stdout | stderr |
|---|---|---|---|
| port_oor (`mk(8080)`, `mk(70000)`) | 0 | `in-range ok` / `UNREACHED` | empty |
| port_in (`mk(8080)`) | 0 | `in-range ok` | empty |
| big_reject (`mk(0x8000_0000_0000_0000)`, `mk(0xFFFF_FFFF_FFFF_FFFF)`) | 0 | `0x8000.. accepted` / `UNREACHED` | empty |
| big_accept (`mk(0x8000_0000_0000_0000)`) | 0 | `0x8000.. accepted` | empty |
| div_zero (`10/5` then `10/0` on `unit Dist: i64`) | 132 (SIGILL) | `10/5 ok` | empty |

The seed's Rust codegen emits no SPL-UNIT-005 / SPL-UNIT-002 guard: out-of-range casts pass, the u64 bound is not enforced, and `x / 0` hardware-traps. This is the seed lowering, not the pure-Simple MIR that the MIR specs cover, so it neither confirms nor refutes the pure-Simple checks. The seed does not implement unit range checks natively (separate gap; the interpreter path does).

## Lane 2: pure-Simple native-build via the seed interpreter (no env var)
    timeout 900 C:/dev/simple/bin/simple.exe native-build test/fixtures/unit_native/port_oor.spl -o build_rbnat2/port_oor_ps.exe
Result: no artifact; killed by timeout, rc=124 after 900 s, last line `workarounds: incomplete coverage; run simple check-dbs --fullscan bugs`, ~8.5k lines of visibility warnings. Matches the known "bare seed native-build interprets native_build_main.spl and never finishes".

## Conclusion
Blocked: no deployed self-hosted native compiler on this host. Re-run the five fixtures with a pure-Simple compiled `simple native-build` once deployed; expected: port_oor panics with SPL-UNIT-005 naming Port and 1..=65535; big_reject rejects 0xFFFF_FFFF_FFFF_FFFF and accepts 0x8000_0000_0000_0000; div_zero exits via SPL-UNIT-002 not SIGILL.
