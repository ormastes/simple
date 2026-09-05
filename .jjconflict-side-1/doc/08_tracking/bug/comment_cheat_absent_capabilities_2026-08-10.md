# Comment-cheat vacuity family #2 — ABSENT capabilities (stream Q5, 2026-08-10)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Specs whose source-scanning needle matches ONLY a comment in the product source.
This record covers the **ABSENT** subset: sites where the capability the spec
claims to prove **does not exist in code at all**. The vacuous needle was the
only thing holding the gate green.

Companion enumeration: `doc/08_tracking/test/comment_cheat_spec_census_2026-08-09.md`.

## Enumeration (re-derived, two independent cross-checks)

| method | raw | deduped |
|---|---|---|
| A — needle paired with nearest preceding product-path literal in the spec | 105 | 60 |
| B — needle searched across **every** product path the spec references (order-independent) | 176 | 119 |
| **A ∩ B (high confidence)** | — | **46 sites / 30 specs** |

A-only (14) are pairing artifacts: the needle is real code in a *different* file the
spec also reads. B-only (73) are needles absent from the paired file but present as a
comment elsewhere — weaker evidence, excluded.

### Scanner correction — the prior census over-counted

The 2026-08-09 census (and the first pass of this one) treated any line whose
trimmed form starts with `*` as a comment. That is a C-family block-comment
continuation rule and it is **wrong for shell**, where `*rust-built*|*rust*seed*)`
and `*) echo "error: ..."` are `case` arms, i.e. executable code. It also
mis-scored `#include` / `#define` in `.c` files as comments when they are
preprocessor directives. Restricting `*`-continuation to `.c/.h/.cpp/.js/.ld/.rs`
and treating `#` in C-family files as code removed **16 false hollow sites**,
including every `simpleos_wm_fullscreen_evidence`, `macos_metal_live_evidence`,
`gui_showcase_perf_artifact_provenance`, `fork_alloc_tracking` and
`thread_alloc_tracking` row. Those gates are sound; the scanner was not.

## Classification

| verdict | sites |
|---|---|
| REAL — capability exists, needle merely anchored on a comment | 31 |
| **ABSENT — capability does not exist (defects below)** | **7** |
| AMBIGUOUS — asserting the comment is deliberate, or the needle is not an assertion | 8 |

## ABSENT — genuine product defects

### D1. ARM64 EL0 handoff concurrency contract is unimplemented (3 sites)

Spec: `arm64_user_exit_return_contract_spec.spl`.
Product: `src/os/kernel/arch/arm64/user_entry.spl:68-69`

```
    # ponytail: one active EL0 handoff per CPU; PID-keyed recorded handoffs and
    # nested kernel resume frames are required before concurrency is enabled.
```

All three needles — `one active EL0 handoff per CPU`, `PID-keyed recorded handoffs`,
`nested kernel resume frames` — match only this deferral comment. The comment states
outright that these properties are *required before concurrency is enabled*, i.e. they
are **not** present. A repo-wide scan of all 58,860 tracked `src/`+`scripts/` files
finds no `handoff_by_pid` / `pid_keyed` / `handoffs_by_pid` symbol of any kind. The
only live entry point is `rt_arm64_enter_recorded_user_live()`, defined nowhere but
`user_entry.spl` itself.

The spec therefore asserts a per-CPU/per-PID handoff contract that no code implements,
and passes because the deferral note happens to contain the words.

**Unblock:** implement per-CPU single-active-handoff tracking and PID-keyed handoff
records, then re-anchor the spec on those symbols. Until then the spec must be RED.

### D2. `rt_syscall_dispatch` — the named live ring-3 syscall path exists nowhere (1 site)

Spec: `simpleos_green_hardware_handoff_blocker_spec.spl`.
Product: `src/os/kernel/ipc/syscall.spl:206`

```
# production". The live ring-3 path is syscall_entry.s -> rt_syscall_dispatch
```

Scanned every tracked file under `src/` and `scripts/` (xargs-fed, with a positive
control needle to prove the scan ran). `rt_syscall_dispatch` occurs **twice in the
entire product tree, and both are comments**:

- `src/os/kernel/ipc/syscall.spl:206`
- `src/os/kernel/arch/x86_64/cpu.spl:126` — *"dispatcher `rt_syscall_dispatch` in
  baremetal_stubs.c"*

There is no definition, no `extern fn` declaration, and no call site. `syscall_entry.s`
does not exist under `src/os` either — the only file of that name in the repo is
`examples/09_embedded/simple_os/arch/x86_64/boot/syscall_entry.s`, which is example
code, not the product.

This is the same shape as the dead GHDL wrapper found in family #1: two comments
describe a live path by name, and a source-grep spec certifies the path exists by
matching the prose that describes it.

**Unblock:** either implement `rt_syscall_dispatch` and wire `syscall_entry.s` into
`src/os`, or correct both comments to name the path that actually runs — and re-anchor
the spec on that symbol.

### D3. ARM/RISC-V QEMU boot lanes have no real-firmware proxy (3 sites)

`.claude/rules/board-runnable.md` requires every QEMU-developed lane to boot via a
real-firmware proxy — OVMF pflash (x86_64), OpenSBI (riscv), EDK2/AAVMF (aarch64) —
and forbids QEMU `-kernel` pass semantics. These three specs anchor on comments that
**document the violation**:

| spec | needle | product | evidence |
|---|---|---|---|
| `boot_smoke_spec.spl` | `-kernel` | `src/os/kernel/arch/arm64/linker.ld:4` | `RAM starts at 0x40000000, kernel loaded by QEMU -kernel flag.` |
| `qemu_runner_spec.spl` | `-kernel` | `src/os/kernel/arch/arm32/boot.spl:12,38` | `On QEMU virt, the kernel is loaded directly with -kernel flag.` |
| `riscv32_boot_qemu_spec.spl` | `RISC-V 32` | `src/os/kernel/arch/riscv32/linker.ld:1` | `QEMU virt machine, direct M-mode boot` / `Kernel loaded at 0x80000000 with -bios none.` |

`-bios none` on riscv32 means **no OpenSBI**; direct `-kernel` on arm32/arm64 means no
EDK2/AAVMF. The aarch64 EFI-stub gap is already acknowledged in `board-runnable.md`;
the arm32 and riscv32 lanes are not, and neither is the fact that specs named
`boot_smoke` / `qemu_runner` / `riscv32_boot_qemu` currently certify these lanes by
matching the comment that admits the bare-boot.

Related, already filed for rv64:
`doc/08_tracking/bug/riscv_qemu_lanes_boot_bare_kernel_without_opensbi_2026-08-09.md`.

**Unblock:** boot arm32/arm64 via EDK2/AAVMF pflash and riscv32 via OpenSBI, keep a
documented physical-board build+boot path per `board-runnable.md`, then anchor these
specs on the firmware-proxy invocation rather than on the memory-map prose. Until then
the specs must be RED and must not be read as board-runnable evidence.

### D4. `AT_EXECFN` auxv entry is absent — the needle matched the comment DENYING it (1 site)

Found while working the REAL list (stream Q10, 2026-08-10). This is the sharpest
instance of the family found so far: the needle is satisfied by the very comment
that states the capability is **not** present.

Spec: `test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:51`
(`expect(source).to_contain("AT_EXECFN")`).
Product: `src/os/kernel/loader/x86_64_fs_exec_ring3.spl:133-134`

```
    # argc, argv+NULL, envp+NULL, then AT_PAGESZ, AT_RANDOM, AT_NULL pairs —
    # exactly the auxv set of the PROVEN clang --version frame (no AT_EXECFN).
```

`_build_sysv_stack_frame` declares exactly three auxv constants — `AT_PAGESZ = 6`
(:102), `AT_RANDOM = 25` (:103), `AT_NULL = 0` (:104) — and writes exactly those
three pairs (:180-185). There is no `AT_EXECFN` constant, no `31`, and no fourth
auxv pair. The local named `execfn_addr` (:158) is the **argv[0] string pointer**,
not an auxv value; the name is itself misleading and is worth renaming.

Re-anchored onto the executable form `val AT_EXECFN: u64 = 31`, so the spec is now
correctly **RED** instead of vacuously green.

**Two candidate resolutions, both needing an owner decision — do not pick one to
get green:**
1. Implement the `AT_EXECFN` auxv pair (constant 31, pointing at the binary-path
   string already written at :161) and bump `fixed_slots` from `+ 6` to `+ 8`; or
2. If the omission is deliberate (the comment claims parity with a PROVEN clang
   `--version` frame), the assertion is wrong and should be dropped — which
   requires approval, per `.claude/rules/testing.md`.

The `test/unit/` twin of this spec has genuinely diverged and does not carry the
needle; only the `test/01_unit/` leg was re-anchored.

## AMBIGUOUS — not defects, do not "fix"

- `sugar_plugin_spec.spl` (2): the `[STATIC-NEXT]` contract asserts marker **comments**
  exist at named sites. Asserting a comment *is* the contract.
- `evalops_export_and_text_at_spec.spl` (3): an `it` block explicitly named
  "documents text .at as a deliberate divergence from the seed" pins the rationale
  comment on purpose.
- `stdlib_intensive_spec.spl` (2): the needles (`/`, `name`) are spec-internal control
  flow (`if line.contains("name"):  # Skip header`), not assertions.
- `mcp_lsp_tools_spec.spl` (1): the spec builds the string under test inside itself and
  asserts against it, never reading the product. A worse defect than comment-cheating,
  out of scope here — it needs rewriting, not re-anchoring.

## Third cross-check (C) — receiver-aware, and why 46 is an UPPER bound

Methods A and B both treat *any* `to_contain("...")` / `.contains("...")` as a
source-text needle. That is wrong in two ways, and manual review of the 46 found
both live:

- **The receiver is often not source text.** `simplebox_build_spec.spl` asserts on
  `simplebox_native_build_cmd("x86_64-unknown-none").contains(...)` — the return
  value of a product function. `ghdl_riscv32_mailbox_spec.spl` asserts on
  `adapter.runner_path`. `wm_host_freebsd_refusal_spec.spl`'s `host.spl` "needle"
  is a *path argument* to `file_exists` / `source_contains`, not a needle at all.
  None of these can comment-cheat; they never grep a product file.
- **Negative assertions invert the meaning.** `core_c_bootstrap_runtime_capsule_
  contract_spec.spl:43` is `expect(source.contains("bin/" + "simple")).to_equal(false)`
  — an *absence* check. A comment-only match is the correct and desired state.

Scan C therefore requires: positive assertion, and a receiver bound to
`read_file`/`read_text`/`read_source` of a literal product path (or the
`source_contains(path, needle)` form). It reports **7 sites / 2 specs** — a strict
lower bound, since it cannot follow needles routed through helper functions or
non-literal paths.

**Honest bracket: 7 (C, strict) ≤ true comment-cheat count ≤ 46 (A ∩ B).** The
"~46" headline is an upper bound, not a count. The ABSENT defects D1-D3 above were
each confirmed by reading the product source directly, so they do not depend on
which bound you take — and scan C independently reconfirms D2, surfacing a second
comment-only symbol alongside it:

| spec:line | needle | product | verdict |
|---|---|---|---|
| `simpleos_green_hardware_handoff_blocker_spec.spl:219` | `rt_syscall_dispatch` | `src/os/kernel/arch/x86_64/cpu.spl:126` | ABSENT (D2) |
| `simpleos_green_hardware_handoff_blocker_spec.spl:218` | `kernel_syscall_entry_asm` | `src/os/kernel/arch/x86_64/cpu.spl:127,176` | ABSENT — same defect, second symbol |

That spec also anchors three needles on **doc/ tracking files** (its own bug record
and a report), not on product source at all — asserting that a bug document still
contains a given heading. That is a fourth vacuity shape and is out of scope here.

### Scanner false-positive modes, for whoever automates this gate

1. `*`-prefixed line is a comment only in C-family files; in shell it is a `case` arm.
2. `#` in `.c`/`.h` is a preprocessor directive, i.e. code.
3. The receiver must be verified to hold file source before a needle counts.
4. Negative assertions (`to_equal(false)`, `to_be_falsy`) must be excluded.

## Standing note

Do not resolve any ABSENT row by relaxing or deleting the spec. A correctly-failing
spec is a legitimate artifact (`.claude/rules/testing.md`). The fix is the missing
capability.

---

# Stream Q24 (2026-08-10) — working the corrected 101-row worklist

Input: `doc/08_tracking/test/spec_hollow_needle_worklist.tsv` (101 deduped rows,
commit `3795acc2b77`). 23 rows were already settled by the prior pass
(heavy_work_preflight, macos_gui_live_window_gate_source, simpleos_crypto_random_gate,
context_ponytail_mimic, riscv_product_ports_source, x86_64_fs_exec_spawn = fixed;
arm64_user_exit_return_contract, simpleos_green_hardware_handoff_blocker, boot_smoke,
qemu_runner, riscv32_boot_qemu = ABSENT/filed; sugar_plugin, evalops_export_and_text_at,
stdlib_intensive, mcp_lsp_tools = AMBIGUOUS) and were skipped. 78 rows remained.

## The headline finding: the 101-row list is still ~75% scanner false positives

Four MORE comment-detection defects were found and fixed in
`scripts/check/census-spec-vacuity.spl`, each with a control fixture:

| # | defect | effect | commit |
|---|---|---|---|
| 4 | **Markdown headings read as comments.** `.md/.json/.html/.txt/.csv/.tsv/.xml/.rst` have no `#` line-comment syntax, but they fell through `is_comment_line`'s unknown-extension branch, which treats any `#`-prefixed line as a comment. `doc/` is a product root, so every spec asserting a heading in a plan/tracking document (`"## Go Profile Evidence Agent"`, `"## Parallel Peak RSS"`, …) was reported HOLLOW. **~30 of the 78 rows.** | false HOLLOW | `e46ebc94f10` |
| 5 | **`to_be(false)` not recognised as an absence assertion.** `is_negative_assertion` knew `to_equal(false)` only. `stage4_final_symbol_closure_spec.spl:1035` is `expect(source.contains("runtime_dynload.c")).to_be(false)` — a comment-only match is the *desired* state there. | false HOLLOW | `04fe443860b` |
| 6 | **Receiver never checked per assertion.** `reads_source_text` is a whole-FILE test: one `file_read` anywhere in a spec licensed every needle in it. So subprocess stdout (`timeout_spec.spl:50` → `process_run("echo",["hello"])`), product-function return values (`native_link_hardening_spec.spl:179` → `native_all_gnu_support_args(...)`; `riscv_fpga_linux_spec.spl:40` → `proof_acceptance_markers()`) and spec-local literals (`test_runner_simple_spec.spl:197` → `name.contains("_test.")`; `bootstrap_intensive_spec.spl:144`) were all reported HOLLOW although none of them ever greps a product file. Needles now require a receiver bound to a read call, directly or via a zero-arg helper that reads within 12 lines; identifier matching is token-boundary aware (a plain substring test matched `a` inside `to_contain`). | false HOLLOW | `73bd1b72eab` |
| 7 | **The spec's own comment lines were harvested for needles.** `check_entry_target_routing_contract_spec.spl:7` had ALREADY been re-anchored by an earlier stream; its explanatory comment quotes the needle it removed (``Was `to_contain("a source")` ``) and the scanner re-reported it. | self-perpetuating row | `73bd1b72eab` |

Defects 1-3 were the previous round; the pattern is now five rounds deep. The
practical rule for anyone reading a hollow-needle list: **a HOLLOW row is a
hypothesis, not a finding.** Every row in this stream that was accepted was
confirmed by reading the product file directly.

## ABSENT — new genuine defects

### D5. SimpleOS cross-build wrappers lost their pure-Simple provenance needle (REAL, fixed)

`test/01_unit/os/native_build_compiler_provenance_spec.spl:10-11` asserted
`SIMPLE_BUILD_COMPILER:-bin/release/simple` in
`scripts/os/simpleos-native-build-aarch64.shs` and `-riscv64.shs`. That string
now occurs in each file **exactly once, inside the comment recording its
removal** (`aarch64.shs:30`, `riscv64.shs:28`). Both wrappers were upgraded to a
seed-rejecting, capability-probing selection — so the capability is present in a
*stronger* form and the spec was simply stale. Re-anchored onto
`simple_compiler_select --root "$REPO_ROOT" --builder-target "$TARGET"`
(aarch64:37-38) and `is_bootstrap_seed` / `compiler_can_build_target`
(riscv64:98,101,105); all anchors pre-checked as non-comment source. Example is
green. Commit `e08d256d8ba`.

### D6. Lint entrypoints are NOT wired to the staged workspace-root audit helper (ABSENT, already RED)

`test/01_unit/app/workspace_root_write_guard_spec.spl:37` (and its identical
twin `test/unit/app/workspace_root_write_guard_spec.spl:37`) assert
`read_file("src/app/cli/lint_entry.spl").contains("cli_run_lint")`.

`cli_run_lint` **does not occur in `src/app/cli/lint_entry.spl` at all.** The
entrypoint dispatches to `run_lint_command(filtered_args)` (`lint_entry.spl:64`);
`cli_run_lint` is defined at `src/app/io/_CliCommands/run_commands.spl:206` and
called from `src/app/build/cli_entry.spl:54`. The scanner called the row HOLLOW
because the needle appears as a comment in `src/app/io/cli_ops.spl:394`, which is
another file the spec reads — a defect-3 residue.

Measured: `bin/simple test test/01_unit/app/workspace_root_write_guard_spec.spl`
→ `Results: 7 total, 5 passed, 2 failed`; the two failures are
"wires lint entrypoints to the staged audit helper" and "wires tracked CLI lint
to staged audit". **This spec is already correctly RED** — the workspace-root
write guard is not reached from the `simple lint` entrypoint. Left RED.

**Unblock:** route `src/app/cli/lint_entry.spl` through the staged audit helper
(`_cli_run_workspace_root_guard()`), or state which entrypoint is authoritative
and re-anchor the spec there.

### D7. The RISC-V QEMU HTTP smoke scripts do not exist (ABSENT, already RED)

`test/system/simpleos_riscv_network_gate_spec.spl` and its
`test/03_system/os/` twin read `scripts/qemu_rv64_http_test.shs` (lines 102, 129,
264) and `scripts/qemu_rv32_http_test.shs` (line 277) and assert the whole
deferred-boundary contract against them (`--expect-deferred`,
`--expect-http-only`, `PMM OK`, `HEAP OK`, `--backend llvm`, …).

**Neither file exists, and neither has ever existed at that path** (`git log --
scripts/qemu_rv64_http_test.shs` is empty; no `scripts/*rv64*`/`*rv32*`/`*riscv*`
file exists). Measured: `Results: 18 total, 8 passed, 10 failed`. Already
correctly RED; recorded here because it is a **distinct vacuity shape** — a spec
whose assertions target a path that does not exist. Per `.claude/rules/board-runnable.md`
this also means the RV32/RV64 QEMU HTTP lanes have no runnable harness at all.

## Nonexistent-path family (new, own shape)

Sweep over all 57 specs in the worklist, restricted to path literals appearing on
a line with a read/exists call, filtering shell-glob and fixture placeholders:

| spec:line | path asserted | status |
|---|---|---|
| `test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:117` | `src/compiler/80.driver/driver/incremental.spl` | missing |
| `test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:252` | `src/compiler/80.driver/driver/parallel.spl` | missing |
| `test/01_unit/os/.spipe_wrapped_entry_qemu_runner_spec.spl:159` | `scripts/mlk_s02_100t_generated_linux.shs` | missing |
| `test/03_system/feature/usage/multicore_green_agent_plan_spec.spl:139` | `doc/06_spec/test/03_system/feature/usage/multicore_green_tracking_spec.md` | missing |
| `test/03_system/feature/usage/multicore_green_tracking_spec.spl:625` | `doc/06_spec/test/05_perf/stress/multicore_green_fanout_spec.md` | missing |
| `test/system/simpleos_riscv_network_gate_spec.spl:102,129,264` | `scripts/qemu_rv64_http_test.shs` | missing (D7) |
| `test/system/simpleos_riscv_network_gate_spec.spl:277` | `scripts/qemu_rv32_http_test.shs` | missing (D7) |

Excluded as legitimate: `test/unit/os/qemu_runner_spec.spl:108,111`, where the
missing paths sit behind `rt_file_exists(...)` guards in a shim-install helper.

This family deserves its own gate — it is invisible to the hollow-needle scan,
because "absent" and "comment-only" are different verdicts and only the latter is
reported.

## Defect 8 (found after the D-table above) and D8 — a second exact-inversion

### Scanner defect 8: `examples/` and `test/` were not product roots

`product_root_prefixes()` listed only `src/ scripts/ tools/ config/ bin/ doc/`.
A needle asserted against a file under `examples/` or `test/` therefore had that
file **dropped from the candidate set** and was scored against whatever other
paths the spec happens to read. Two confirmed false HOLLOWs:

- `test/03_system/check/wm_multiapp_taskbar_spec.spl:179` — `GuiRenderer.create`
  is executable code at `examples/06_io/ui/wm_multiapp_taskbar_gui.spl:120`.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.spl:169`
  — receiver reads `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`.

Adding a root only ever ADDS candidates, so it can only turn a false HOLLOW into
"code". Fixed in `3923a1991ee`.

### D8. WebSocket opcode dispatch — the spec asserted the construct the product FORBIDS (REAL, fixed)

The sharpest instance in this stream, sharper than D4.

`test/02_integration/app/ui.web/ws_e2e_spec.spl:187-192` (and its identical twin
`test/integration/app/ui.web/ws_e2e_spec.spl`) asserted
`case WS_OPCODE_TEXT` … `case WS_OPCODE_PONG` against
`src/lib/nogc_sync_mut/http/ws/ws_parser.spl`.

All six needles matched **only the comment at `ws_parser.spl:248-257`, which
exists to forbid exactly that construct**:

```
    # Opcode dispatch MUST use explicit equality, NOT `match`.
    # WS_OPCODE_* are `val` i64 constants (ws_frame.spl), not enum variants.
    # In `case` position a bare identifier is an IRREFUTABLE BINDING PATTERN
    # ... so `match header.opcode:` with `case WS_OPCODE_TEXT:` bound *every*
    # opcode to the first arm and made the other five arms dead
```

The real dispatch is `if/elif header.opcode == WS_OPCODE_*` at `:258-287`. The
adjacent `it "rejects unknown opcodes"` asserted `case _:`, which occurs
**nowhere in the file at all** — that leg was already correctly RED.

Re-anchored onto the six equality arms and the fall-through
(`return _build_pong_frame(header, payload)` plus the trailing `return nil`),
all pre-checked non-comment; the `it` was retitled from "in the match dispatch"
to "in the equality dispatch". Both twins fixed, both examples green
(`46 total, 45 passed, 1 failed`; the remaining failure — SHA-1 accept
computation — is pre-existing and untouched). Commit `928f1737b4c`.

## Standing recommendation

`doc/08_tracking/test/spec_hollow_needle_worklist.tsv` was generated before
defects 4-8 were fixed and must be **regenerated** before anyone works it
further —
`SIMPLE_TIMEOUT_SECONDS=0 bin/simple run scripts/check/census-spec-vacuity.spl --list`
(the CPU guard SIGTERMs it at 60s otherwise; it runs for tens of minutes under
the interpreter). Expect the row count to fall sharply: of the 78 rows this
stream actually examined, every one inspected was either a scanner false
positive, already fixed by a prior stream, or one of the three genuine findings
recorded above.

## New vacuity shape: a NEGATIVE assertion against a MISSING file always passes

`test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl` reads
`src/compiler/80.driver/driver/incremental.spl` (:117) and
`src/compiler/80.driver/driver/parallel.spl` (:252). **The whole
`src/compiler/80.driver/driver/` directory does not exist** — the modules live in
`driver_build/`, and `class LegacyBuildCache:` occurs nowhere in `src/compiler/`.

The consequence is asymmetric and worth naming, because it is the same asymmetry
as the value-type-helper family (#3):

- the two POSITIVE legs (`expect(driver_src).to_contain("class LegacyBuildCache:")`
  :119, and `to_contain("if all_done and not self.ready_queue.contains(dep_id):")`
  :254) are correctly RED;
- but the SIX negative legs (:120-126, `expect(driver_src.contains(X)).to_equal(false)`)
  **pass vacuously** — a missing file contains nothing, so every absence
  assertion against it is trivially satisfied.

The prior stream's scan-C rule "negative assertions cannot comment-cheat, exclude
them" is correct for comment-cheating and **wrong as a general vacuity
exclusion**: a negative assertion is vacuous whenever its receiver is empty,
whether from a missing path, a failed read, or a renamed module. A future gate
should assert that every path passed to a read call exists, independently of
needle classification — the 7-site table above is the seed for it.

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN. `src/os/kernel/arch/arm64/user_entry.spl` still carries, inside
`dispatch_enter_user_blocking_live`, the comment:
"# ponytail: one active EL0 handoff per CPU; PID-keyed recorded handoffs and
nested kernel resume frames are required before concurrency is enabled."
The capability is still absent from the tree — the comment documents a missing
implementation, which is the comment-cheat ABSENT pattern this doc names.
