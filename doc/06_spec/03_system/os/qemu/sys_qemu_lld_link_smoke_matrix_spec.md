# sys_qemu_lld_link_smoke_matrix_spec

> QEMU System Test — SimpleOS in-guest toolchain smoke matrix (lane C5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_lld_link_smoke_matrix_spec

QEMU System Test — SimpleOS in-guest toolchain smoke matrix (lane C5).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMPLEOS-SELFHOST-C5 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — SimpleOS in-guest toolchain smoke matrix (lane C5).

As a SimpleOS developer, I want to compile, link and RUN real C and C++
programs entirely inside a SimpleOS guest booted from real firmware, so that
"hello world on the SimpleOS terminal" is a reproducible transcript rather
than a claim.

Every row of the matrix below drives the same real-firmware board proxy the
proven `clang -cc1` ladder uses: OVMF pflash boot (never QEMU `-kernel` pass
semantics — `.claude/rules/board-runnable.md`), sshd in ring 3, and a direct
absolute-path FS-exec of the tool. The link step invokes `lld` DIRECTLY, never
through the clang driver, because the ring-3 FS-exec path has no `fork`.

Guest filesystem constraint, load-bearing for every row: SimpleOS FAT32
`fat32_write_file` is ROOT-DIRECTORY-ONLY with 8.3 names (no mkdir, no LFN
create). Reads traverse subdirectories, writes do not. So every staged input
and every produced artifact is an uppercase 8.3 name in the ROOT: `/LLD.ELF`,
`/CLANG.ELF`, `/HELLO.C`, `/HELLO.O`, `/HELLO.ELF`, `/CRT0.O`, `/LIBC.A`,
`/SIMPLEOS.LD`, `/LIBCXX.A`.

Fail-closed contract, mirroring `sys_qemu_x86_64_fs_exec_spec.spl`: a row is
classified as `pass`, `missing-media:<path>`, or `boot-fail:<marker>`, and
anything other than `pass` is a RED failure. `skip()` is NEVER used — while
the cross LLVM toolchain is still building, these rows stay VISIBLE and RED
with a printed `blocked` diagnosis naming the exact missing artifact, so the
matrix can never be mistaken for green.

Driver: `scripts/os/ssh_lld_link_uefi.shs` (rungs 3-6) and the C5 extensions
noted per row. Plan: `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`
lanes C4/C5; ladder: `doc/03_plan/os/in_guest_lld_link_ladder.md`.

## Scenarios

### SimpleOS in-guest toolchain smoke matrix (C5)

#### the in-guest link ladder has a stager and a gate script committed

- the in-guest link ladder has a stager and a gate script committed
- Locate the multi-payload FAT32 stager for the guest image
- Locate the rungs 3-6 in-guest link gate script
- Confirm the SimpleOS sysroot supplies crt0, libc and the linker script


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the in-guest link ladder has a stager and a gate script committed")
step("Locate the multi-payload FAT32 stager for the guest image")
assert_true(rt_file_exists(image_stager()))
step("Locate the rungs 3-6 in-guest link gate script")
assert_true(rt_file_exists(link_gate_script()))
step("Confirm the SimpleOS sysroot supplies crt0, libc and the linker script")
assert_true(rt_file_exists(crt0_path()))
assert_true(rt_file_exists(libc_path()))
assert_true(rt_file_exists(linker_script_path()))
```

</details>

#### compiles, links and runs hello.c entirely inside the guest

- compiles, links and runs hello.c entirely inside the guest
- Stage /HELLO.C, /CRT0.O, /LIBC.A, /SIMPLEOS.LD, /CLANG.ELF and /LLD.ELF as root 8.3 names
- Boot SimpleOS under OVMF pflash and reach the ring-3 sshd accept loop
- Run /CLANG.ELF -cc1 -emit-obj /HELLO.C -o /HELLO.O over SSH as a direct FS-exec
- Run /LLD.ELF -flavor gnu -T /SIMPLEOS.LD -o /HELLO.ELF /CRT0.O /HELLO.O /LIBC.A -- lld directly, never via the clang driver, because ring-3 FS-exec has no fork
- Run /HELLO.ELF from the guest filesystem and read its stdout and exit status
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles, links and runs hello.c entirely inside the guest")
step("Stage /HELLO.C, /CRT0.O, /LIBC.A, /SIMPLEOS.LD, /CLANG.ELF and /LLD.ELF as root 8.3 names")
step("Boot SimpleOS under OVMF pflash and reach the ring-3 sshd accept loop")
step("Run /CLANG.ELF -cc1 -emit-obj /HELLO.C -o /HELLO.O over SSH as a direct FS-exec")
step("Run /LLD.ELF -flavor gnu -T /SIMPLEOS.LD -o /HELLO.ELF /CRT0.O /HELLO.O /LIBC.A -- lld directly, never via the clang driver, because ring-3 FS-exec has no fork")
step("Run /HELLO.ELF from the guest filesystem and read its stdout and exit status")
val classification = classify_row(
    "hello-c-compile-link-run",
    [clang_static_path(), lld_static_path(), crt0_path(), libc_path(), linker_script_path()],
    [
        "accept loop start",
        "persist HELLO.O -> OK",
        "LLD ",
        "-o /HELLO.ELF",
        "persist HELLO.ELF -> OK",
        "heap:stream-open-ok path=/HELLO.ELF",
        "returned rc="
    ]
)
_diagnose("hello-c-compile-link-run", classification)
expect(classification).to_equal(SYSTEST_PASS)
```

</details>

#### links a two-translation-unit C program in-guest

- links a two-translation-unit C program in-guest
- Stage /HELLO.C and /HELLO2.C, where HELLO.C calls a function defined in HELLO2.C
- Compile each translation unit separately in-guest to /HELLO.O and /HELLO2.O
- Link both objects in one /LLD.ELF -flavor gnu invocation against /CRT0.O and /LIBC.A
- Run the linked /HELLO.ELF and confirm the cross-TU call produced the expected output
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("links a two-translation-unit C program in-guest")
step("Stage /HELLO.C and /HELLO2.C, where HELLO.C calls a function defined in HELLO2.C")
step("Compile each translation unit separately in-guest to /HELLO.O and /HELLO2.O")
step("Link both objects in one /LLD.ELF -flavor gnu invocation against /CRT0.O and /LIBC.A")
step("Run the linked /HELLO.ELF and confirm the cross-TU call produced the expected output")
val classification = classify_row(
    "two-tu-c-link",
    [clang_static_path(), lld_static_path(), crt0_path(), libc_path(), linker_script_path()],
    [
        "accept loop start",
        "persist HELLO.O -> OK",
        "persist HELLO2.O -> OK",
        "/HELLO.O /HELLO2.O",
        "persist HELLO.ELF -> OK",
        "heap:stream-open-ok path=/HELLO.ELF",
        "returned rc="
    ]
)
_diagnose("two-tu-c-link", classification)
expect(classification).to_equal(SYSTEST_PASS)
```

</details>

#### links a C++ hello against libc++.a in-guest

- links a C++ hello against libc++.a in-guest
- Stage the C++ standard library archive as /LIBCXX.A -- '+' is not a legal 8.3 character, so libc++.a cannot keep its host name
- Compile the C++ source in-guest with /CLANG.ELF -cc1 -x c++ to /HELLO.O
- Link /HELLO.O against /LIBCXX.A and /LIBC.A with /LLD.ELF -flavor gnu
- Run the linked /HELLO.ELF and confirm the C++ runtime initialised and printed
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("links a C++ hello against libc++.a in-guest")
step("Stage the C++ standard library archive as /LIBCXX.A -- '+' is not a legal 8.3 character, so libc++.a cannot keep its host name")
step("Compile the C++ source in-guest with /CLANG.ELF -cc1 -x c++ to /HELLO.O")
step("Link /HELLO.O against /LIBCXX.A and /LIBC.A with /LLD.ELF -flavor gnu")
step("Run the linked /HELLO.ELF and confirm the C++ runtime initialised and printed")
val classification = classify_row(
    "cxx-hello-libcxx",
    [clang_static_path(), lld_static_path(), libcxx_path(), crt0_path(), linker_script_path()],
    [
        "accept loop start",
        "-x c++",
        "/LIBCXX.A",
        "persist HELLO.ELF -> OK",
        "heap:stream-open-ok path=/HELLO.ELF",
        "returned rc="
    ]
)
_diagnose("cxx-hello-libcxx", classification)
expect(classification).to_equal(SYSTEST_PASS)
```

</details>

#### produces host-identical objects at -O0 and -O2 from the same preprocessed TU

- produces host-identical objects at -O0 and -O2 from the same preprocessed TU
- Preprocess the source on the host with the cross clang into a single self-contained /TU1.I
- Compile /TU1.I in-guest at -O0 and retrieve the object with the proven getfile path
- Compile /TU1.I in-guest at -O2 and retrieve that object as well
- Byte-compare each retrieved object against the host cross build of the SAME .i at the SAME optimisation level
- Confirm -O0 and -O2 differ from each other, so the flag was actually honoured in-guest
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces host-identical objects at -O0 and -O2 from the same preprocessed TU")
step("Preprocess the source on the host with the cross clang into a single self-contained /TU1.I")
step("Compile /TU1.I in-guest at -O0 and retrieve the object with the proven getfile path")
step("Compile /TU1.I in-guest at -O2 and retrieve that object as well")
step("Byte-compare each retrieved object against the host cross build of the SAME .i at the SAME optimisation level")
step("Confirm -O0 and -O2 differ from each other, so the flag was actually honoured in-guest")
# This row's oracle is a REAL host-side byte-compare of the retrieved
# objects, not a serial marker: a marker could only prove the command
# ran, never that the bytes agree.
val classification = classify_row(
    "o0-vs-o2-byte-compare",
    [
        clang_static_path(),
        host_ref_o0(), host_ref_o2(),
        guest_out_o0(), guest_out_o2()
    ],
    ["accept loop start", "persist TU1.O -> OK"]
)
_diagnose("o0-vs-o2-byte-compare", classification)
expect(classification).to_equal(SYSTEST_PASS)
val g0 = rt_file_read_bytes(guest_out_o0()) ?? []
val g2 = rt_file_read_bytes(guest_out_o2()) ?? []
val h0 = rt_file_read_bytes(host_ref_o0()) ?? []
val h2 = rt_file_read_bytes(host_ref_o2()) ?? []
assert_true(_bytes_equal(g0, h0))
assert_true(_bytes_equal(g2, h2))
assert_false(_bytes_equal(g0, g2))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `124ce1ebfecb89ae947856a5245cb42b9696ce0dcb002c77bb6ef5b092bb741a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `124ce1ebfecb89ae947856a5245cb42b9696ce0dcb002c77bb6ef5b092bb741a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `124ce1ebfecb89ae947856a5245cb42b9696ce0dcb002c77bb6ef5b092bb741a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.spl
mirror: doc/06_spec/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the in-guest link ladder has a stager and a gate script committed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.spl:170:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles, links and runs hello.c entirely inside the guest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.spl:196:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links a two-translation-unit C program in-guest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
