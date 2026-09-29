# Target 5 exact hello link and matched C size (Linux ARM64)

Status: the **development hello size comparison passes** with exact captured
link inputs. BS7 release admission, optional-provider closure, NoGC inventory,
and 30/100-sample production cohorts remain open.

The isolated Target 5 branch built a fresh pure-Simple Stage4 compiler from
866 selected-K1 source units (zero failures, 102.94 seconds, 1,408,312 KiB
peak RSS). Its executable SHA-256 is
`5e7225d7f2d687400039d56da6f9a061231e695e914d78889ac2c5a0a538313f`.
The Stage4 compiler passed `--version`, compiled the one-source hello with
`--aot --O1 --no-debug`, and returned exit 0. The hello ran and printed
`Hello World` with exit 0.

The opt-in Linux LLD capture saved the exact response and opened inputs as
`build/target5-capture-stage4/hello-link.tar` (SHA-256
`6dcc9bc1e62adda05238b723d1af82c84277a16405e7765fe5e59dd643794055`).
Its sidecar binds the unstripped hello SHA-256
`fcf5d4bb072c107f0e2603db7c5f864117c06cd9ba01b84e60b33cf8fda41e7a`
and linker SHA-256
`3b2e366d1a5bcdd2e305a6f4997e809e8af2c46b84469c1a6b496337591a1833`.
Replaying the captured `response.txt` with the same `ld.lld` produced a
byte-identical Simple executable.

The C comparator in
`doc/09_report/compiler/evidence/target5_hello_same_entry_object_20260929.c`
defines only the same `__simple_main` entry and calls `rt_println_str` for the
same output. Its source SHA-256 is
`284d73566ca32d57389bcf36454259d911827d7c400c9ba72343385772808ba2`.
The C response differs from the captured Simple response at exactly two
lines: the output filename and this one program object. Both links use the
captured Simple startup object, runtime objects, CRT objects, libc, linker,
`--gc-sections`, `--icf=all`, PIE, and the same strip tool. Both list the same
dynamic `NEEDED` libraries (`libc.so.6` and the AArch64 loader).

| Output | Unstripped bytes | Stripped bytes | SHA-256 of stripped output |
| --- | ---: | ---: | --- |
| Simple hello | 21,448 | 13,544 | `ab850125235c1540ed63e25854fa21e79a2fd7f0dde7e5dca03330366e381b1c` |
| Matched C hello | 21,704 | 13,608 | `ee698556d50c8f6a86e7f18f1db60bf23c63586373a9de8933aa22b8993694e7` |

The stripped Simple output is **64 bytes smaller**, with a Simple/C ratio of
**0.995297**, below both the 15,360-byte absolute and 1.05x matched-C size
limits. The new
`scripts/check/check-runtime-binary-size-matched-link.py` independently
replays both links, verifies the captured archive/output/linker hashes,
checks the two strip outputs and runtime output, and enforces both size
limits. It also requires both program objects to define only `__simple_main`
and import only `rt_println_str`, preventing a second `main` from replacing
the archived startup wrapper. The final checker passed on the actual
captured archive after the symbol-contract hardening.
A changed C stripped file was rejected
as `c-strip-replay-mismatch`; a changed archive receipt was rejected as
`archive-digest-mismatch`. A C object that also defined `main` was rejected
as `hello-object-symbol-contract-invalid`.

The BS7 producer/checker now require this replay on Linux and bind the
unstripped outputs, C source, archive, capture receipt, and tool hashes in
the cohort receipt. A real-LLD fixture passes the producer and checker and
rejects collector/provider, Stage4, sample-count, binary, label, archive,
receipt, and sample-binary-hash mutations. The cohort also binds the supplied
Python executable hash; every sample row must match its lane's executable.
This result qualifies the exact **size comparison only**. The existing
30-pair Simple/Python startup and RSS diagnostic used the same stripped
Simple SHA-256, but it did not capture the required NoGC inventory or
provider trace and is not a BS7 admission. Fresh production cohorts,
100-sample release qualification, and full optional-provider feature closure
remain required.

The executable SPipe wrapper was attempted with this Stage4 compiler, but its
older flat AST bridge rejected declaration nodes within a 40-file source closure
before either scenario ran. The shell mutation fixture passed; the SPipe
wrapper remains unverified.
