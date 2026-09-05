# riscv64 freestanding runtime: `text.len()` wrong and in-loop string accumulation loses content (2026-08-31)

Status: OPEN. Blocks running real toolchain components (caret, MCP, linter,
test runner) in-guest on SimpleOS riscv64.

## How this was found

Bringing the toolchain components up in-guest on riscv64 under real OpenSBI
v1.4 firmware (`-bios fw_payload`, never `-kernel`, never `isa-debug-exit`).
The caret row — `app.llm_caret.json_helpers` + `app.llm_caret.redact` — linked
and started, printed its built message, and then **stalled with no trap
message**:

```
[components] SimpleOS riscv64 in-guest toolchain components (OpenSBI fw_payload)
[components] serial up, exercising real product modules
[caret] built message: {"role":"user","content":"CARET_RTT_CONTENT"}
```

`examples/09_embedded/simple_os/arch/riscv64/text_primitive_probe_entry.spl`
was written to bisect the text primitives that `json_find` /
`extract_json_string` depend on, one at a time, printing after each so the last
line printed names the culprit. Built by the RUST SEED (the pure-Simple
compiler cannot compile anything in this tree yet) and run in-guest under the
same real-firmware chain. Literal captured output:

```
[probe] subject: {"role":"user"}
[probe] step 1: len()
[probe] len = WRONG
[probe] step 2: substring(0, 6)
[probe] substring(0,6) = {"role
[probe] step 3: substring(1, 5)
[probe] substring(1,5) = "rol
[probe] step 4: equality
[probe] equality = EXPECTED
[probe] step 5: bounded scan
[probe] scan found index = EXPECTED
[probe] step 6: trim + starts_with
[probe] trim = EXPECTED
[probe] starts_with = EXPECTED
[probe] step 7: chars() iteration
[probe] chars count = EXPECTED
[probe] step 8: single-arg substring
[probe] substring(8) = "user"}
[probe] step 9: char accumulation
[probe] accumulated = Q
PROBE_TEXT_PRIMITIVES_SIMPLEOS_RISCV64_DONE
```

## Defect 1 — `text.len()` returns a value that does not compare equal to its length

`.len()` lowers to `rt_len` (`src/compiler_rust/compiler/src/codegen/llvm/
functions/calls.rs:2091,2271` and `emitter.rs:278`). The baremetal
implementation is `examples/09_embedded/simple_os/arch/riscv64/boot/
baremetal_runtime_core.inc.c:481`, which returns the RAW byte count:

```c
if (hdr->type == HEAP_STRING) return (RuntimeValue)((RuntimeString *)hdr)->len;
```

The probe reported `len = WRONG` against **two different expectations** (14 on
the first run, then 15 after the expectation itself was corrected — the subject
`{"role":"user"}` is 15 bytes, counted longhand in the probe's comment). Two
different wrong answers rule out an off-by-one in the probe and point at an
encoding mismatch: `rt_len` hands back a raw integer while the comparison site
treats the result as a tagged value (`ENCODE_INT(v) == (v << 3) | TAG_INT`).
Note the same file is already internally inconsistent about this —
`rt_index_get` (line 491) *requires* `IS_INT(index)`, i.e. an ENCODED index,
while `rt_string_char_at` casts its index raw.

This is the caret stall: `json_find` (`src/app/llm_caret/json_helpers.spl:128`)
loops `while i <= slen - nlen` with `slen = s.len()`, so a wrong `slen` makes
the bound garbage and the scan runs away. The loop is the only one in that call
path, and every primitive in its body (substring, equality) probes EXPECTED.

**Do NOT fix by blanket-encoding `rt_len`'s return** without re-probing: the
array paths that already work read it raw, so the fix has to establish which
convention codegen actually emits for this call site and make the whole file
agree, rather than flipping one function.

## Defect 2 — accumulating a string inside a loop (partly explained, not closed)

Codegen does **not** lower `acc = acc + x` inside a loop to repeated
`rt_string_concat`. It rewrites it into a STRING BUILDER — a probe that added
two more accumulation loops failed to link with `rt_string_builder_new`,
`rt_string_builder_push`, `rt_string_builder_finish`, `rt_string_data` and
`rt_string_len` all undefined. Those five are now ported into
`baremetal_runtime_core.inc.c` (fourth tranche), which removes the link
failure, but the ports have NOT been proven correct in-guest: the refined probe
that would have exercised them did not get a clean build-and-boot cycle before
this session ended, and the transcript below is from the run BEFORE they
existed. Treat the ports as unverified.

The original symptom, still unexplained on its own terms:

Step 9 accumulates over `"user"}` with `acc = acc + ch`, mapping `"` to `Q`.
Expected `QuserQ}`; got **`Q`** — a single character. Step 7 separately proves
the iteration itself is fine (`chars count = EXPECTED`, 5 of 5), so the loop
runs the right number of times and it is the ACCUMULATION that does not carry
forward. This is the shape `extract_json_string` uses to build its result, and
it is a general hazard for any product module that builds a string in a loop.

Not yet root-caused. Suspects, in order: `rt_string_concat`'s result handling
under the freestanding bump allocator, and value-semantics/COW handling of a
`var` rebound from its own value each iteration.

## Scope note — what is NOT broken

`substring` (`rt_slice`, both two-arg and open-ended), text equality, `trim`,
`starts_with`, and `chars()` iteration all probe EXPECTED in-guest. The
firmware chain, the seed cross build, and in-guest execution are all healthy:
`scripts/check/check-simpleos-riscv64-hello-world-in-guest-opensbi.shs` reports
`PASS — 1 program(s) checked ... 67 serial line(s)`.

## Reproduces on a SECOND component, which raises the severity

After the runtime ports below landed, the test-runner row
(`testrunner_component_entry.spl`, calling the real
`parse_test_output`) also links, boots, and stalls at the same kind of place:

```
[components] SimpleOS riscv64 in-guest toolchain components (OpenSBI fw_payload)
[components] serial up, exercising real product modules
[testrun] feeding a 3-example spec transcript to the real parser
```

`parse_test_output` scans its transcript with `.len()`-bounded loops, exactly
like `json_find`. Two independent product modules stalling at their first
`.len()`-bounded loop, with every other probed primitive EXPECTED, is what
promotes defect 1 from "caret's problem" to the single blocker standing between
this lane and three green component rows.

## The string-builder tranche is SUSPECT — do not treat it as good

After the builder ports landed, `text_primitive_probe_entry.spl` builds cleanly
(no undefined symbols) and the firmware boots — `OpenSBI v1.4` and the full
banner reach the serial log — but the guest emits **zero** `[probe]` lines. It
dies or hangs before its very first `serial_println`, which is earlier than any
probe step. The probe is the entry that leans hardest on in-loop string
accumulation (steps 9a/9b/9c), i.e. the builder path.

This is NOT universally fatal: the devtool row links the same runtime, boots,
and passes (see below). But the probe's regression from "boots and prints
through step 9" to "prints nothing" happened across the builder tranche and
nothing else, so the builder is the prime suspect. Investigate before relying
on it — likely candidates are the `HEAP_STRING_BUILDER` tag colliding with
something that walks heap objects by type, or `rt_string_len` / `rt_string_data`
now shadowing a path that startup code depended on.

Consequence for this record: **defect 2 is not diagnosed.** The transcript
quoted above predates the builder and the refined 9a/9b/9c split has never
produced output. What is known is only that codegen lowers in-loop accumulation
to a builder, and that the naive port of that builder does not work.

## What DID reach green

`devtool_component_entry.spl` — the real lint rule
`lint_os_freestanding_patterns`, run in-guest under the same real-firmware
chain — is a complete, non-vacuous round-trip:

```
[components] serial up, exercising real product modules
[devtool] lint src/os/probe_clean.spl  (expect no findings)
[devtool] lint src/os/probe_dirty.spl  (expect a finding)
[devtool] finding: entry-closure defect C1: module-global val/var initialized from a call expression is never emitted under freestanding codegen and stays nil — move the call into an explicit ensure/init function invoked from entry; see doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md
COMPONENT_DEVTOOL_SIMPLEOS_RISCV64_OK real lint rule ran in-guest, clean snippet silent and dirty snippet flagged
[components] all component rows exited rc=0
```

The clean snippet stayed silent and the dirty one produced the rule's real
message, so this passes in both directions rather than by always agreeing. It
also shows the runtime ports are sound enough to carry a real product module —
the remaining stalls are specific defects, not a broadly broken runtime.

## Related gap (separate, larger)

`--entry-closure` over the four components' combined module graph leaves ~500
`rt_*` symbols undefined (sqlite, tcp, process, threads, SIMD, filesystem,
time). Caret alone needed only 8, which were ported into
`baremetal_runtime_core.inc.c` in the same change as this record
(`rt_string_ends_with`, `rt_string_char_code_at`, `rt_text_cmp_any`, `rt_slice`,
`rt_string_join`, `rt_for_iterable`, `rt_value_int`, `rt_value_unbox_int` — all
ports of the existing hosted ABI in `src/runtime/runtime_native.c`, not new
symbols). MCP additionally needs `rt_closure_new` / `rt_closure_func_ptr`
(closure support, required by `DispatchEntry.handler`), which is the deepest of
the remaining items.

## Update 2026-08-31 — measured on the PR #173 base (u64 `.len()` ABI fix)

All evidence below is in-guest on SimpleOS riscv64 under real OpenSBI v1.4
`fw_payload` (`-bios` only; no `-kernel`, no `isa-debug-exit`), seed-built.

### #173 DOES clear the stalls
Caret and the test runner no longer hang. Both rows now run to completion and
reach `[components] parking`. The failure moved from a hang to a wrong answer.

### Two further defects found and FIXED here
1. **`rt_string_builder_push` had the wrong signature.** The riscv64 port took
   `(builder, data, len)` and cast argument 2 to `const char *`. The hosted
   contract (`runtime.h:405`), the codegen ABI
   (`runtime_sffi.rs:515`, `rt_string_builder_push(I64, I64) -> I64`) and the
   aarch64 sibling (`freestanding_runtime.c:408`) all say TWO arguments whose
   second is a tagged string HANDLE. Codegen's 2-argument call therefore copied
   the string object's HEADER bytes with a garbage length. Probe step 9a printed
   32 NUL-ish bytes and step 9b hung; after the fix they print `xxxxxxx` and
   `yyyyy` and the probe reaches `PROBE_TEXT_PRIMITIVES_SIMPLEOS_RISCV64_DONE`.
2. **The closure ports had the wrong parameter widths.**
   `runtime_sffi.rs:678-681` declares `rt_closure_new(I64, I32)`,
   `rt_closure_set_capture(I64, I32, I64) -> I8`,
   `rt_closure_get_capture(I64, I32)`; the Rust runtime agrees (`u32` index,
   `value/objects.rs:177,198,213`). The port had used 64-bit parameters, leaving
   the upper register half undefined. Corrected to `uint32_t` / `int8_t`.

### STILL OPEN — appending a `chars()` element ends the loop after one iteration
Probe step 9d was added specifically to separate the two variables that step 9c
confounds (a branch, and a loop-variable append). It appends the loop variable
with NO branch:

    var acc_d = ""
    for ch in tail.chars():
        acc_d = acc_d + ch

With `tail` = `"user"}` this must print `"user"}`. It prints a single `"` —
the first character only. Step 9c (same append, with an `if`) likewise yields
one character. Meanwhile 9a and 9b, which append a LITERAL in the same loop
shapes, are byte-correct. So the defect is **not** branch/phi lowering: it is
that appending a runtime-produced string (a `chars()` element) inside the loop
that is iterating that same `chars()` array stops the loop after one pass.

This is the remaining cause of both red rows: caret's `extract_json_string` and
the test runner's `parse_test_output` are exactly this pattern, which is why
caret reports `extracted content=` (empty) and the runner reports neither
`passed=2` nor `failed=1`.

### STILL OPEN — the mcp row traps
The mcp row traps before its first `println`, inside
`id_path_intern` / `DispatchRegistry` / `dispatch_wrap`. The CPU re-enters the
guest entry: across 373,249 serial lines the OpenSBI banner appears exactly
ONCE, so this is a trap re-entry, not a firmware reset. The closure ABI fix
above was necessary but not sufficient — the trap survives it. Ruled out:
defect C1 (no module-level `val`/`var` initialised from a call exists in
`id_path.spl`, `authority_token.spl` or `mcp/dispatch.spl`).
