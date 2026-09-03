# arm64 lane: the parse failures are a STALE DEPLOYED SEED, not bad sources (2026-09-01)

Status: **ROOT CAUSE IDENTIFIED**. Supersedes the diagnosis in
`arm64_desktop_engine2d_media_chain_blockers_2026-09-01.md` § "Still blocked" item 4.

## The prior diagnosis was wrong on both sites

That record attributed the seed's parse rejections to the arm64 server-payload
sources themselves:

- `src/os/userlib/fs.spl:537` — "the only multi-line `export a, b,` /
  continuation form in `src/os/`: expected expression, found Dedent".
- `src/os/apps/dbd/dbd.spl` — "expected expression, found Newline".

Neither holds.

### 1. Multi-line `export` is NOT the problem — the seed supports it explicitly

Minimal fixture, compiled with the deployed seed, exit 0:

```
fn alpha() -> i64:
    return 1
fn beta() -> i64:
    return 2
export alpha,
    beta
```

The Rust seed hand-consumes Newline/Indent/Dedent inside a comma-continued
export list — `src/compiler_rust/parser/src/stmt_parsing/module_system.rs:820-845`
(`parse_export_use`), comment: *"Skip newlines and indents after comma to
support multi-line export lists"*. `fs.spl:537` is well within that.

### 2. The real failure is in the STDLIB, not in `src/os/`

`simple compile src/os/userlib/fs.spl` reports:

```
parse: in ".../src/lib/common/encoding/utf8.spl":
  Unexpected token: expected Newline, found Identifier { name: "rt_text_count_codepoints_cached" }
```

The failing file is `src/lib/common/encoding/utf8.spl` — a stdlib dependency —
and the failing construct is a **single-line `unsafe` suite body** at
`utf8.spl:255` (also `:260`, `:265`):

```
unsafe(capabilities: [ffi]): rt_text_count_codepoints_cached(s)
```

Reduced fixture, RED on the deployed seed with the identical message:

```
extern fn rt_text_count_codepoints_cached(s: text) -> i64

fn f(s: text) -> i64:
    unsafe(capabilities: [ffi]): rt_text_count_codepoints_cached(s)
```

The indented form of the same code parses fine — confirming the gap is the
inline suite, not the capability list.

The originally-reported line number (21, the multi-line braced
`use std.encoding.simd_text_ffi.{...}`) is a **misreported location**: prefix
fixtures of `utf8.spl` lines 1-25 parse clean. The seed points at the first
occurrence of the identifier's *name*, not the failing token's site. That
misdirection is what sent the prior lane at the `use`/`export` forms.

## This is case (a) — a parser bug — and it is ALREADY FIXED IN SOURCE

`src/compiler_rust/parser/src/unsafe_inline_body_test.rs` exists at
`origin/main` and pins this exact defect, quoting the exact error text:

> `unsafe(capabilities: [...]): expr` with a ONE-LINE body was rejected with
> "expected Newline, found Identifier": `parse_unsafe_block_primary` called
> `parse_block`, which accepts only the indented form. This is the shape used
> at 8+ sites in `src/os/kernel/boot/mmio_hardware.spl`, which had been
> expanded to indented blocks as a workaround.

The fix (`parse_inline_or_block`, `src/compiler_rust/parser/src/parser_helpers.rs:178`)
landed **2026-08-30** (`9d74c705e53`). The deployed seed binary
`bin/release/x86_64-unknown-linux-gnu/simple` was built **2026-08-26** — four
days earlier. It predates its own regression test.

**So: no product source should be reformatted, and no parser fix needs
writing. The deployed seed binary is simply stale relative to its own source
tree.** The regression test already ships in the parser crate; a redeploy is
the whole fix.

## Consequence for the "bootstrap redeploy" question

A full pure-Simple bootstrap redeploy (to clear the stage-binary SEGV,
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`) is
strategically still needed, but it is **not required to unblock this gate**:
the runner's designed fallback parses the server payload with the Rust seed,
and rebuilding the seed from `origin/main` un-stales that path.

## Separate, genuine finding: self-hosted parser lacks multi-line `export`

While the seed supports comma-continued `export`, the **self-hosted** parser
does not — `src/compiler/10.frontend/core/parser_decls_use.spl:380-383`
(`parse_export_decl`) breaks out of its item loop on any non-comma token and
never skips Newline/Indent. **56 `.spl` files under `src/` use the multi-line
form.** This is a real bootstrap divergence that a redeploy will hit, and it
matches the "found Dedent" signature the prior record reported — but against
the self-hosted parser, not the seed. Filed here for whoever performs the
redeploy; out of scope for this lane.

## Resolved: the `get_arm64_wm_qemu_target()` spec contradiction

The prior record left this open. It is settled: **the two `wm_entry.spl`
assertions are stale; the production-render contract spec is correct and is
currently RED because the SOURCE is what lags.**

Evidence chain:

1. `src/os/_QemuRunner/runner_targets.spl:545` still has
   `entry: "examples/09_embedded/simple_os/arch/arm64/wm_entry.spl"`, with
   `output: "build/os/simpleos_arm64_wm.elf"`. The predicate
   `_is_arm64_wm_qemu_target` (`os/_QemuRunner/os_build_run.spl:712-714`, and its
   mirror at `src/os/qemu_runner_part2.spl:628`) matches the same string.
2. `wm_entry.spl` is explicitly **legacy**:
   `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs:4` —
   *"The old implementation built arch/x86_64/wm_entry.spl, a hand-drawn legacy…"*.
3. **x86_64 already completed this migration**: `runner_targets.spl:720`
   `get_desktop_gui_target()` uses `arch/x86_64/gui_entry_desktop.spl`.
   arm64 is lagging a finished migration.
4. **Decisive**: the arm64 readiness gate has ALREADY migrated —
   `scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs:8,88` sets
   `ENTRY=.../arch/arm64/gui_entry_desktop.spl`. So the lane *script* builds
   `gui_entry_desktop.spl` while the QEMU *target* still names `wm_entry.spl`.
   That is an internal inconsistency in the product, not in the contract spec.
5. History: the contract spec's intent-bearing commit is `f2ffa11a188`
   *"feat(simpleos): require process-owned arm and riscv desktops"* — newer than
   the substantive commits behind the two asserting specs (`ae55a746719` /
   `6f86ff32a7d`, `f12958a4d51`). It is a **requirement** spec, deliberately
   written ahead of the source.
6. Both entries exist; `get_arm64_desktop_engine2d_target()`
   (`runner_targets.spl:558-573`) already uses `gui_entry_desktop.spl`.

Correct fix (NOT applied here — it repoints the shared `arm64-wm-ramfb` lane,
which cannot be revalidated until a kernel builds, and is not needed for the
Engine2D gate):

1. `runner_targets.spl:545` — `entry:` -> `.../arch/arm64/gui_entry_desktop.spl`,
   KEEPING `output: "build/os/simpleos_arm64_wm.elf"` (the contract spec asserts
   exactly that pairing, and the `output` is what keeps the predicate
   distinguishable from the engine2d target).
2. `os_build_run.spl:713` and the mirror `qemu_runner_part2.spl:628` — same
   string swap so the predicate keeps matching.
3. `test/01_unit/os/qemu_runner_extended_spec.spl:301` and
   `test/03_system/gui/arm64_wm_qemu_contract_spec.spl:156` — expect
   `gui_entry_desktop.spl`. Their `target.output` assertions stay valid.

## Verified: rebuilding the seed clears the whole parse wall

Rebuilt `cargo build --release --bin simple` from `origin/main`
(`1b12bd36bc8`) into a lane-private `CARGO_TARGET_DIR`; the shared seed at
`/mnt/data/worktrees/simple-main/bin/release/...` was NOT overwritten.

RED-before / GREEN-after, same five inputs, same command
(`simple compile <f> -o /dev/null`), exit status captured directly:

| input | deployed seed (2026-08-26) | rebuilt seed (2026-09-01) |
|---|---|---|
| inline `unsafe(capabilities: [ffi]):` fixture | `parse: expected Newline, found Identifier` | **rc=0** |
| `src/lib/common/encoding/utf8.spl` | `parse: expected Newline, found Identifier` | no parse error |
| `src/os/userlib/fs.spl` | `parse: expected Newline, found Identifier` | no parse error |
| `src/os/apps/dbd/dbd.spl` | `parse: expected Indent, found Self_` | no parse error |

Residual, narrower gap (reported, not fixed): the **capability-less** inline
form `unsafe: expr` still fails with `expected Newline, found Identifier` on
the rebuilt seed. `unsafe_inline_body_test.rs` only covers the
`unsafe(capabilities: [...])` spelling. Worth a follow-up fixture.

## Where the arm64 build now stands

With the rebuilt seed (`SIMPLE_BUILD_COMPILER=<rebuilt>`), plus
`scripts/os/simpleos-core-archive.shs --backend cranelift` (parts_built=19,
parts_failed=0) and `scripts/os/simpleos-sysroot-aarch64.shs` (clean, `crt0.o`
+ core objects present), `simple os build --scenario=arm64-desktop-engine2d
--timeout 1200` gets **all the way through discovery and parsing** and now
fails at CODEGEN, on two files, with the kernel ELF still not produced:

```
FAILED FILES (2):
  - src/os/apps/dbd/dbd.spl: codegen: 1 function body/bodies failed to
    compile: [DbdLiveClientSessionV1.create]
  - src/os/apps/dbd/dbd_provisioning.spl: codegen: 1 function body/bodies
    failed to compile: [DbdProvisioningOwnerV1.ready]
Build failed: native-build aborted: 2 file(s) failed to compile
```

`SIMPLE_ALLOW_STUB_FALLBACK` was NOT set.

Both are **source** defects (case (b)), pre-existing and
**architecture-independent** — they were simply unreachable behind the parse
wall. Neither is arm64-owned; `src/os/apps/dbd/` is the shared server payload.

1. **`dbd_provisioning.spl:113` `ready()` omits `self.` on five field reads.**
   It mixes qualified and bare access in one expression:
   ```
   pub fn ready() -> bool:
       self.state == DbdProvisioningStateV1.Admitted and provider.configured and
           credential.len() == 0u64 and credential_wiped and
           cert_chain.len() > 0u64 and private_key.len() > 0u64
   ```
   `self.state` is qualified; `provider`, `credential`, `credential_wiped`,
   `cert_chain`, `private_key` are not. Every other method in the file uses
   `self.`. Codegen is right to say `unresolved identifier 'provider'`.
   Fix: qualify all five. **FIXED in this change**, with RED/GREEN evidence:
   pre-fix `native-build --target aarch64-unknown-simpleos` reports
   `unresolved identifier 'provider'`; post-fix the
   `DbdProvisioningOwnerV1.ready` body failure is gone (0 occurrences). The
   file still fails for defect 2 below, which is why the gate does not move.

2. **`DbdTransactionOwnerV1` is imported and used but DEFINED NOWHERE.**
   `dbd.spl:45` imports it from `os.apps.dbd.dbd_protocol`; it is used as a
   field type at `:197` and constructed at `:208` via `.new()`; `:226` calls
   `.clear()` on it. A repo-wide scan finds **only those three references and
   no definition**:
   ```
   /usr/bin/grep -rn 'DbdTransactionOwnerV1' src/ --include=*.spl
     src/os/apps/dbd/dbd.spl:45    (import)
     src/os/apps/dbd/dbd.spl:197   (field type)
     src/os/apps/dbd/dbd.spl:208   (DbdTransactionOwnerV1.new())
   ```
   This is a **half-landed change** of exactly the shape PR #249 fixed for
   `SimpleOsPlatformBuildTarget`: the consumer half landed, the class half
   never did. Not fixed here — the intended API (`new()`, `clear()`, and its
   role in `DbdTransactionQueueStatusV1`) needs the owning lane's design
   intent, and inventing it in a shared server payload mid-lane risks
   clobbering that work.

## Answer to "is a bootstrap redeploy the real fix?"

**Not for the parse blocker** — that was purely a stale deployed binary, and a
`cargo build` of the seed already in the tree clears it. A redeploy IS still
required for the separate, filed stage-binary SEGV
(`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`): all four
tracked stage binaries still report `skip (failed native-build --target probe)`,
so nothing but the seed can serve this lane, and
`scripts/lib/simple-compiler-select.shs:301` deliberately refuses the seed
unless `SIMPLE_BUILD_COMPILER` names it explicitly.

## Gate status

Unchanged and still honest — the kernel does not exist, so the gate cannot run:
`ERROR — nothing was checked: arm64 desktop/WM kernel missing:
build/os/simpleos_arm64_desktop_engine2d.elf`.
The `protocol: linux` AAVMF -> BOOTAA64.EFI -> kernel.elf handover therefore
remains **UNPROVEN**. Do not record it as proven.

## Decisive: the attested kernel build REQUIRES a bootstrap redeploy

The gate's own remediation hint names
`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`. Run with
the rebuilt seed it refuses outright, before reaching any source:

```
arm64_desktop_engine2d_attested_build_status=fail
arm64_desktop_engine2d_attested_build_reason=compiler-version-invalid
```

That is by design: the attested lane will not accept the Rust bootstrap seed as
the producing compiler, and `scripts/lib/simple-compiler-select.shs:301` skips
it for the same reason. So even with the parse wall gone and the dbd defects
hypothetically fixed, **this kernel cannot be attested-built until a
pure-Simple compiler that passes `native-build --target
aarch64-unknown-simpleos` is deployed.**

**Stating it plainly, as asked: a bootstrap redeploy IS necessary here.** It is
not a workaround for the parse errors (those were the stale binary, now
understood and reproducible), it is a hard precondition of the attested build
path this gate depends on. It is blocked on
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md` — all four
tracked stage binaries fail the target probe.

## Verbatim gate verdict (unchanged, rc=2)

```
[arm64-wm-vulkan] selftest OK (25 fixtures)
ERROR — nothing was checked: arm64 desktop/WM kernel missing: build/os/simpleos_arm64_desktop_engine2d.elf — build it first with scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
```

The gate and its 25 selftest fixtures were not modified or weakened.

## Ordered remaining work

1. Bootstrap redeploy (a pure-Simple compiler passing the aarch64
   `native-build --target` probe). Hard precondition; owned by the bootstrap
   lane. Note it will then hit the self-hosted multi-line `export` gap above
   (56 files).
2. ~~Fix `DbdProvisioningOwnerV1.ready()`~~ — DONE in this change.
3. Define `DbdTransactionOwnerV1` (or remove its consumer half) — needs the dbd
   lane's design intent.
4. Repoint `get_arm64_wm_qemu_target()` per the resolution above.
5. Only then can the `protocol: linux` AAVMF handover be tested. It stays
   UNPROVEN until it is.

## Repo-wide implication — NOT an arm64 problem

The shared deployed seed
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(built 2026-08-26) predates the 2026-08-30 parser fix. `utf8.spl` is a stdlib
dependency of nearly everything, so **every lane compiling current stdlib
through that binary inherits this same parse wall.** It was not redeployed from
this lane — other lanes are running against it mid-session and replacing it
underneath them would be unsafe. Flagged as an action item for whoever can
coordinate the swap: a plain `cargo build --release --bin simple` is sufficient.
