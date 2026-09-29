# Target 5 literal hello matched `puts` size (Linux ARM64)

Status: the selected NFR-002 **matched C ratio and absolute-size sublimits**
pass for the current-source one-source literal `hello` fixture. The build used
`--O1 --no-debug`; an admitted `release-small` profile, BS7 startup/RSS,
NoGC/provider evidence, unwind proof, and full optional-provider closure
remain open.

The pure-Simple Stage4 compiler (SHA-256
`5e7225d7f2d687400039d56da6f9a061231e695e914d78889ac2c5a0a538313f`)
built `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` with
`--aot --O1 --no-debug`. The executable exited 0 and printed exactly
`hello\n`. Its captured LLD archive has SHA-256
`129969cfe4457e1723e38c5e5a873b966111c35bb55ff2fb2dd8637dbcfc91b9`.

The C entry in
`doc/09_report/compiler/evidence/target5_literal_hello_puts_20260929.c`
defines only `__simple_main` and calls `puts("hello")`. The replay replaces
only the program object; startup, runtime, CRT, linker flags, section GC,
LLD, and strip tool are identical. The checker independently replays both
links and requires both programs to emit the bytes in
`doc/09_report/compiler/evidence/target5_literal_hello_stdout_20260929.txt`.

| Output | Unstripped bytes | Stripped bytes | Stripped SHA-256 |
| --- | ---: | ---: | --- |
| Simple literal hello | 21,448 | 13,544 | `e758ebdc43590e71b7e48be5628d287038a5fc75f8bd79328ad5386f26d46214` |
| Matched C `puts` hello | 21,080 | 13,264 | `39bdbcb69ccfc357df1cbfc8bf6bafa1ca82cc54efff1f17a10824fb2b954163` |

Simple/C is **1.021110**, below 1.05, and Simple is below 15,360 bytes.
The earlier 0.995297 comparison used C's `rt_println_str` and is retained as
a same-writer diagnostic, not the selected NFR-002 denominator.

The literal Simple object imports `rt_println_str`; the C object imports
`puts`. The unstripped Simple ELF has no retained
`rt_string_new_literal`, `rt_to_string`, or `rt_literal_intern_table` symbol.
It still has `.eh_frame`, `.eh_frame_hdr`, `.init_array`, and `.fini_array`,
so the release-small unwind/constructor gate is not established.

The BS7 producer/checker now bind expected stdout bytes and separate the
NoGC hello binary from the interpreter startup binary. Their focused real
LLD shell fixture passed with those two changes, including stdout tampering
and binary-hash mutations. One earlier run reported an unnamed accepted
mutation; a traced rerun and the final changed fixture passed. The selected
C `puts` source was changed afterward. Its exact literal-link checker passed,
but the full shell mutation fixture has not been rerun after that source
change under this session's three-cycle limit. None of these results is a
production cohort qualification.
