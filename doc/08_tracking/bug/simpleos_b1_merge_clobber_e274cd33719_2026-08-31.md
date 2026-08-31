# B1: SimpleOS kernel unbuildable — root cause is the share-history merge clobber, not stale idioms

Filed 2026-08-31. Status: OPEN (partial repair landed in-worktree).

## Summary

`scripts/check/check-enterprise-store-in-guest-ovmf.shs` cannot build its kernel.
The failures were attributed to "stale source idioms that are now hard errors"
(erased-receiver field access, paren-less `.length`). That attribution is wrong
for the dominant class. Two independent causes were measured:

1. **A stale seed binary**, which manufactured an entire phantom failure class.
2. **A landed merge clobber** in `e274cd33719`, which deleted the definitions the
   failing modules call — including security-critical ELF admission checks.

## Cause 1 — stale seed manufactures phantom parse failures

The lane defaults to `SEED=src/compiler_rust/target/release/simple`. The
checked-out binary on this host was dated **2026-08-27 23:38**, predating parser
fixes that are already present in the source tree: `is_statement_start` in
`src/compiler_rust/parser/src/parser_impl/core.rs` now lists `Underscore`,
`Self_`, and the literal/expression-start token kinds (added by the 2026-08-26
and 2026-08-28 fixes, whose own comments name
`authenticated_fs_exec_submission_service_v1.spl` as the motivating file).

Measured on the stale seed: **34 distinct files fail to PARSE** — 32 under
`src/os`, plus `src/lib/common/encoding/utf8.spl` and
`src/lib/common/math/math.spl` — with `Unexpected token: expected Indent, found
Underscore / Self_ / Identifier{TypeName} / FString(...)`. Minimal reproduction
(`build/scratch/f4.spl`): an `if` whose condition wraps after `or` onto a line at
the same column as the body, where the body's first statement begins with `_ =`.
The same shape with a `return` body parses fine on both seeds, which is what made
the class look like an arbitrary source rule.

After `cargo build --release --bin simple` from the current tree (2m45s), **all
34 parse failures disappear**. No source change was required or made for this
class. Anyone measuring B1 against the checked-in seed is chasing ghosts; this is
the likeliest explanation for the earlier "19 modules" and "12 phantom timeouts"
counts.

Recommendation: the lane should refuse a seed older than the parser sources it
was built from, or version-stamp it, rather than silently using whatever binary
is on disk.

## Cause 2 — `e274cd33719` reverted mainline work

`e274cd33719` "chore: merge all share-history worktree branches into main"
resolved in favour of its **second** parent and dropped mainline content. Over
`src/os` it is 979 files, +63151/-44886. The follow-up `e9da588ee61`
"fix(merge): repair 1136 unparseable .spl files from the share-history merge" is
232 files, +17119/-15636 — i.e. the "repair" was itself substantially deletion.

Proof for the first traced case, `src/os/kernel/loader/elf_loader.spl`:

    e274cd33719^1  fn elf_authenticated_layout_v1 = 1   (mainline)
    e274cd33719^2  fn elf_authenticated_layout_v1 = 0   (branch)
    e274cd33719    fn elf_authenticated_layout_v1 = 0   (merge took the branch)
    HEAD           fn elf_authenticated_layout_v1 = 0

That single file lost 109 lines: `ExecutableElfLayoutV1`,
`elf_authenticated_layout_v1`, the whole `stage_x86_64_user_elf` staged-load API
and its seven `staged_x86_64_*` accessors, and — security-relevant — the **W^X
check** ("ELF PT_LOAD is writable and executable"), the **PT_LOAD
segment-overlap check**, and the **PT_LOAD alignment check**, replaced by a
`for segment in image.segments` rewrite that simply omits them. The only three
lines HEAD had added were a trailing-whitespace artifact, that check-dropping
loop rewrite, and an `export` line the mainline version already carried.

**Consequence beyond the build: SimpleOS x86_64 executable admission has been
running without W^X and segment-overlap enforcement since that merge landed.**

### Why the "erased receiver" diagnosis was wrong

`hir: cannot infer field type ... struct 'ANY' field 'load_ranges'` at
`executable_admission_pipeline.spl:367` (`layout.unwrap().load_ranges`) reads
like the documented erased-receiver limitation in `.claude/rules/language.md`,
whose stated workaround is an intermediate typed `val`. It is not that. The
receiver is `ANY` because the callee `elf_authenticated_layout_v1` **does not
resolve — it exists nowhere in the tree**. Introducing a typed `val` would have
required naming a type that no longer exists, i.e. fabrication. For this class,
`struct 'ANY'` means *unresolved callee*, and the fix is restoration.

## Measured failing-module list (fresh seed, `--timeout 1200`)

28 modules, 0 timeouts, 0 parse errors. Classes:

| n | class |
|---|---|
| 20 | `hir: Unsupported feature: cannot infer field type while lowering <fn>: struct <S> field <f>` |
| 6 | `codegen: N function body/bodies failed to compile` (`GlobalLoad: unresolved identifier <local>`) |
| 1 | `mir: Unsupported HIR construct: unknown variant or method 'NetSocketCreate' on enum CapabilityKind` |
| 1 | `hir: Cannot infer field type: struct 'TaskCapRecord' field 'session_id'` |

Restoring `elf_loader.spl` from `e274cd33719^1` took this to **26**
(`executable_admission_pipeline.spl` and `executable_x86_32_mapping_owner_v1.spl`
now lower cleanly; `executable_arm32_mapping_owner_v1.spl` advanced to a
different missing symbol).

## Correction — `NetSocketCreate` was a clobber, not a never-existed symbol

An earlier revision of this record claimed `CapabilityKind.NetSocketCreate` had
never existed. **That claim was wrong, and the way it was reached is the
cautionary tale.** It came from tracing only four revisions on one branch line
(`e274cd33719^1`, `^2`, the merge, `e9da588ee61`) and finding 0 at each. A
`git log -S NetSocketCreate --all` immediately finds the introducing commit
`af1408f34a4` "feat(simpleos): model socket creation and endpoint bind
authority", which defines both `NetSocketCreate` and `NetBindIpv4(address: u32,
port: u16)` in `src/os/kernel/types/capability_types.spl` — deliberately
appended after all existing variants, with a comment saying so to keep enum
ordering stable.

**Lesson for this whole class: a four-rev trace is not sufficient evidence of
"never existed."** There is more than one clobber commit in this history (see
below), so an absence at any chosen pair of revisions proves nothing. Always run
`git log -S <symbol> --all` before concluding a symbol was never written.

`capability_types.spl` lost 24 lines relative to `af1408f34a4`. Restored from
that commit. HEAD's *only* real addition over it was this, in the capability
path-prefix check:

    -    if required_path[0:held_prefix.len()] != held_prefix:
    -        return false
    -    if required_path.len() == held_prefix.len():
    -        return true
    -    required_path[held_prefix.len()] == "/"
    +    required_path[0:held_prefix.len()] == held_prefix

That "addition" is a **path-prefix privilege escalation**: the mainline form
requires a path-component boundary, so a capability over `/etc` does not grant
`/etcpasswd`; HEAD's raw prefix match grants it. The restore deliberately does
NOT preserve HEAD's line.

The five production sites that request the variant —
`syscall_net_portable_v1.spl:81` (`ipc.cap_check`), `web_launch_grants.spl:77`,
`fs_exec_launch_caps_v1.spl:46`, `dbd_launch_grants_v1.spl:57`,
`server_launch_grants.spl:147` — are therefore correct code whose declaration was
deleted out from under them, not dead code coded against a fictional API.

## Additional clobber commits found

`e274cd33719` is not the only one.

- **`4edef8fab8e` "snapshot current development state"** — a whole-working-copy
  snapshot that rewound the sshd tree (~2465 net-deleted lines; `ssh_session.spl`
  lost 8 struct fields plus `SshExecTxV1`, and
  `arm64_ssh_request_context_owner.spl`, 445 lines, was deleted outright). This is
  exactly the failure mode `.claude/rules/vcs.md` § "Sync must never clobber"
  describes.
- **`af1408f34a4` .. HEAD** — `capability_types.spl`, above.
- **Dangling `_partN` facades.** `e274cd33719` rewrote ~21 facade files to
  `export use <name>_part1/2/3.*` where those modules **do not exist** — the real
  split files live in sibling `_ClassName/` folders. A dangling facade erases its
  entire exported API downstream, which is why one defect produced *both*
  `struct 'ANY' field 'X'` and `codegen: GlobalLoad: unresolved identifier`.
  This is the single largest contributor to B1: e.g. all three `VirtioBlkDriver`
  codegen failures were one dangling `os.drivers.virtio.virtio_blk` facade, fixed
  without touching any of the three modules that reported them. **54 dangling
  re-exports across ~21 facades were counted; 4 are repaired here, 17 facades
  remain** (`io/cli_commands`, `io/cli_compile`, `cli_debug/commands`,
  `mcp/assistant/session_store`, `traceability/core`, `ui/render/tui_widgets`,
  `ui/web/taskbar_runtime`, `wm_compare/html_compat`, `apps/file_explorer`,
  `apps/shell/{shell_app,shell_tools}`, `port/bootstrap_cross`,
  `services/llm/mcp_os_server`, `tls13/{cert_verify,tls13}`,
  `tools/net/ssh_tool`, `userlib/window`), each a 3-6 line restore.

## Security-relevant content recovered by the restores

Beyond making the build work, these restores put back enforcement that had been
silently deleted:

- `elf_loader.spl` — W^X, PT_LOAD segment-overlap, PT_LOAD alignment checks.
- `capability_types.spl` — path-component boundary in the capability prefix check.
- `cpio_newc.spl` — path canonicalization, duplicate detection, entry-type and
  hardlink checks, hex validation, size limits.
- `rt_net_socket_facade.spl` — port-range validation, listener tracking, the
  `RT_NET_READ_EXACT_MAX` bound and over-read check.
- `nvme_queue.spl` — `rt_dma_sync_for_device` / `rt_dma_sync_for_cpu` cache
  maintenance.

Each of these is a live correctness/security regression that predates B1 and is
independent of whether the kernel builds.

## A capability function was being silently stubbed

While iterating, the build log showed:

    [CODEGEN BODY] Function 'capability_set_from_sandbox_lowering' body compilation
      failed: GlobalLoad: unresolved identifier 'local_tid'
    [CODEGEN-STUB-FALLBACK] body compilation failed for
      'capability_set_from_sandbox_lowering'

`src/os/kernel/ipc/capability.spl:520` used a counter `local_tid` that its own
docstring describes ("token_id is assigned sequentially starting at 1 within this
function ... they use a local counter") but that was **never declared**. This is
pre-existing at HEAD, not introduced by any restore here — it was simply masked,
because the module previously died earlier on the `TaskCapRecord.session_id`
error and never reached codegen.

The dangerous part is the second line. Under the lane's
`SIMPLE_ALLOW_FREESTANDING_STUBS=1`, the failure did not fail the build — the
body was replaced by an **empty stub**, i.e. a function that maps sandbox grants
to kernel capabilities would have returned an empty capability set. Same
silent-degradation family as B2b. Fixed by declaring the counter the docstring
already specifies; deliberately minimal, so no emitted token's `token_id`,
`parent_token_id` or `depth` changes.

Separately worth noting: the other three `caps.push(...)` sites in that function
omit `token_id`/`parent_token_id`/`depth` entirely and so take field defaults,
giving `depth: 0` where the `CapabilityToken` docstring says fresh root grants
should default to 2. Not changed here — that is a semantic change needing review,
not a build fix.

## Guard added: restores must not drop declarations

Repairing a clobber means restoring a file from an older revision, and an older
revision can legitimately lack work the current tree added. `.claude/rules/vcs.md`
already says to diff BOTH directions before overwriting;
`scripts/check/check-no-decls-dropped.shs` makes that mechanical. For every
changed `.spl` it fails closed if a top-level declaration present at the base is
missing from the working copy.

It earned its place immediately: it caught the `cpio_newc.spl` restore dropping
`_align4_from`, `cpio_lookup`, `_hex8_to_i64` and `_read_text`. Investigated —
all four are file-local helpers of the clobbered version with **zero** callers
anywhere in `src/` or `examples/` (the same names elsewhere are unrelated
file-local helpers in modules that never import `cpio_newc`), superseded by the
restored implementation's own helpers. Accepted, but only because it was checked
rather than assumed.

## Outcome: B1 is resolved; the build now stops in a different, pre-existing place

After the restores, `enumerate-os-lowering-failures.shs` reports **`failing
modules: 0`** — all 28 `src/os` modules lower and codegen cleanly. B1 as scoped
(modules failing HIR lowering) is closed.

The build now reaches the **link** stage for the first time and fails there, for
a cause that is not B1 and not introduced by any change here (`git status` shows
zero modifications under `examples/` or `src/runtime/`):

    ERROR: failed to compile examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c
    ERROR: failed to compile .../boot/runtime_service_owners.c
    ERROR: failed to compile .../boot/tls13_aes_gcm_helper.c
    ERROR: failed to compile .../boot/up1_dci_uefi_loader.c
    fatal error: too many errors emitted, stopping now

with C errors including `no member named 'gc_flags'`, `call to undeclared
function 'runtime_array_from_abi'`, `call to undeclared function 'x...'`, and
`incompatible integer to pointer conversion`. These hand-written boot C files
have drifted from the runtime headers they include.

The ~30 subsequent `ld.lld: error: ... symbol not found:
kernel__abi__syscall_shim__spl_handle_*` messages are **downstream of that**, not
an independent defect: `baremetal_stubs.c` is exactly the file that provides the
weak default stubs the linker script references (see the header comment of
`src/os/kernel/abi/syscall_shim.spl`), so when it fails to compile every one of
those weak symbols disappears. `syscall_shim.spl` itself is NOT clobbered — it
has 2 `fn spl_handle_` at HEAD, the same count as at `e274cd33719^1`,
`c469a68b211` and `4edef8fab8e~1`; the real per-syscall definitions live in its
eight sibling `syscall_shim_*.spl` files by design.

**Why this was never caught:** `scripts/check/check-c-runtime-compiles-push.shs`
scans `src/runtime/` only. The SimpleOS boot C under
`examples/09_embedded/simple_os/**` is outside every existing gate, so it can rot
indefinitely. Extending that guard's roots is the obvious follow-up and is not
done here.

## The dangling-facade class, fixed tree-wide (42 instances, 19 facades)

`scripts/check/check-no-dangling-reexports.shs` enumerated the class exactly:
**42 dangling `export use <mod>_partN.*` re-exports across 19 facade files**,
under `src/os`, `src/app`. All 42 are now repaired; the guard reports
`PASS — 0 _partN re-export(s) present across 8982 module(s)`.

Repair used `scripts/tool/repair-dangling-reexport-facades.shs`, which is
dry-run by default and refuses to overwrite a facade unless **every** HEAD-only
insertion is itself one of the dangling `_partN` lines — i.e. HEAD added only the
defect. That condition was true for 13 facades outright. The pattern is
consistent: the clobber REPLACED real `_ClassName/` re-exports with `_partN`
lines, e.g.

    -export use os.tls13._CertVerify.der_parsing.*
    -export use os.tls13._CertVerify.hostname_verify.{extract_san_dns_names, ...}
    +export use os.tls13.cert_verify_part1.*

Three more (`tui_widgets`, `html_compat`, `mcp_os_server`) were restorable after
inspection — their extra "insertions" were a reworded comment and one further
`_partN` line.

**Three needed surgery, not restoration, and this is the important caveat.**
`qemu_runner.spl`, `simpleos_multiplatform_build.spl` and `cli_compile.spl` have
base versions that re-export symbols which **no longer exist at HEAD** —
`simpleos_platform_userland_abi`, `simpleos_platform_userland_target`,
`simpleos_platform_userland_firmware_contract`,
`_is_arm64_desktop_engine2d_target`,
`arm64_desktop_engine2d_required_marker_fragments`. Restoring those files
wholesale would have replaced one dangling reference with a different one. They
were fixed by rewriting **only the module path**, keeping HEAD's narrower symbol
lists. Verified by grepping each symbol before writing.

This is the general hazard of clobber repair: the base is usually a superset, but
not always, and "restore the file" is not a safe default. Both guards below exist
to make that check mechanical rather than remembered.

## Hand-merge deviations, reviewed

Three deliberate deviations from the base in `rt_net_socket_facade.spl` were
verified rather than taken on trust:

- **Guest port 22, not the base's 2222** — correct.
  `src/os/apps/sshd/x86_64_sshd_autostart.spl:36` logs
  `port=22 hostfwd=2222`, confirming 22 is the guest-side port and 2222 the host
  forward.
- **`os_fd: i64`, dropping the base's `> 2147483647` narrowing check** — correct.
  The struct's own comment at `rt_net_socket_facade.spl:27-28` says "Opaque RV64
  registry handles are i64 generation-tagged values. Keep them lossless in the
  façade entry rather than narrowing to an OS fd."
- The riscv64 `_rt_net_transport_*` layer kept from HEAD — additive, no base
  conflict.

## Repro / tooling added

- `scripts/tool/enumerate-os-lowering-failures.shs` — builds the entstore kernel
  and prints the failing-module list grouped by error class; full log stays in
  `build/os/entstore/lowering.log`.
- `scripts/tool/sweep-os-parse-errors.shs` + `summarize-os-parse-errors.shs` —
  parse-sweep all 2024 `src/os` `.spl` files in parallel and reduce to the set of
  distinct OFFENDING files (discovery aborts on the first bad file, so a build
  can never enumerate them).
- `scripts/tool/trace-symbol-across-revs.shs` — the clobber-vs-never-existed
  discriminator used throughout this record.
- `scripts/tool/compile-os-modules.shs` — per-module compile check.
  **Known limit:** standalone `simple compile <file>` reports OK for modules the
  real whole-project build rejects, so it is not a substitute for the build.

## Compile-time regression: 7 modules exceed the lane's 300s per-module timeout

Recorded per CLAUDE.md ("when you hit a meaningful perf regression during
implementation or verification, either fix it in the same change or record it as
a concrete bug/todo before moving on"). Not fixed here — the fix is a compiler
cost problem, not a source change.

After the restores, a lane run fails with **7 modules hitting `timeout (300s)`**
rather than any lowering or codegen error:

    src/os/kernel/loader/riscv32_fs_exec_spawn.spl
    src/os/kernel/loader/riscv32_sv32_mapping_owner_v1.spl
    src/os/kernel/loader/x86_32_fs_exec_spawn.spl
    src/os/kernel/scheduler/scheduler_riscv32_executable_adoption_v1.spl
    src/os/kernel/scheduler/scheduler_x86_32_executable_adoption_v1.spl
    src/os/kernel/scheduler/_Scheduler/scheduler_green_lifecycle.spl
    src/os/kernel/scheduler/_Scheduler/scheduler_helpers.spl

The same tree builds these modules with **zero** timeouts when the per-module
budget is raised (`--timeout 1200`), so they cost somewhere between 300s and
1200s each.

`scripts/check/check-enterprise-store-in-guest-ovmf.shs` passes **no** `--timeout`
to `native-build`, so it takes the 300s worker default. That is why the lane
reports `FAIL — kernel build produced no build/os/simpleos_entstore_uefi128.elf`
while the diagnostic build of the identical tree reports `failing modules: 0`.

**Honest attribution:** five of the seven are modules restored here or direct
dependents of `executable_authority_registry.spl`, which the restore grew by
+1221 lines — so this change plausibly pushed them over the line. The other two
(`_Scheduler/scheduler_green_lifecycle.spl`, `scheduler_helpers.spl`) are
byte-identical to HEAD and were not touched by anything here; they are slow on
their own account, and the earlier stale-seed run showed timeouts at this default
too. Both possibilities should be measured before assuming either.

Two candidate follow-ups, neither taken here because each is a real decision
rather than a build fix:
1. Give the lane an explicit `--timeout` (masks the cost, unblocks the lane).
2. Investigate why these modules cost >300s. This smells related to the known
   superlinear-per-file cost recorded for lint in `.claude/rules/commands.md`
   (`zca_rows.spl`), which is also an unlocated compiler cost problem.

## Correction: the boot C is NOT a "drift", and adopting the other lane's fix did not work

An earlier section of this record described the failing boot C as having "drifted
from the runtime headers it includes". That framing was wrong, and so was the
remedy attempted after it.

What is actually true:

- The same clobber hit the x86_64 boot lane. Another session has already fixed it
  in commit **`fcaa4f64215`** "fix(simpleos): restore x86_64 boot-lane sources
  clobbered by merge e274cd33719; audit QEMU boot gates" (2026-08-31 03:32),
  which rewrites `baremetal_stubs.c` (+3108 lines) plus `gui_entry_desktop.spl`,
  `engine2d_baremetal_core.spl` and `simpleos_crt0.S`.
- That commit is **not** in `origin/main` and **not** in this worktree's HEAD. It
  is another lane's in-flight work.
- Adopting those four files into this worktree to unblock verification **did not
  work and was a mistake**. `baremetal_stubs.c` at `fcaa4f64215` also depends on
  runtime-header changes that are not in this HEAD, so it fails with
  `no member named 'gc_flags' in 'HeapHeader'`, `use of undeclared identifier
  'BAREMETAL_GC_BYTE_PACKED'`, and undeclared `x86_aes_repack_bytes` /
  `x86_ssh_aes_gcm_decrypt_packet_tagged` /
  `x86_32_collector_nonce_slot_line_length`. Splicing one file out of another
  lane's branch into an older tree produced a dependency mismatch rather than a
  build.
- The four files have been **reverted** to this worktree's HEAD. Nothing from
  `fcaa4f64215` is carried here.

Consequence for scope: the boot-C half of the clobber is owned by that lane and
must land with its runtime-header prerequisites. It cannot be verified from this
worktree, and this record makes no claim about it beyond naming the commit.

`'efi.h' file not found` in `up1_dci_uefi_loader.c` is a separate, genuine
external-SDK-header case of the kind `check-c-runtime-compiles-push.shs` would
classify as SKIP — not a clobber.

## Final status

- **B1 as scoped — `src/os` modules failing HIR lowering — is fixed.** The
  diagnostic build reports `failing modules: 0`, down from 28.
- **The kernel does NOT build**, and therefore
  `check-enterprise-store-in-guest-ovmf.shs` does not pass. Its literal verdict:

      FAIL — kernel build produced no build/os/simpleos_entstore_uefi128.elf

  Two independent reasons remain, neither of them B1 and neither fixable here:
  1. the boot-C clobber owned by `fcaa4f64215` (above);
  2. the 300s per-module timeout (below), which fails the lane on modules that
     compile cleanly given a larger budget.
- Claims in this record rest on `--timeout 1200` runs. The lane uses the 300s
  default, so "failing modules: 0" is a statement about lowering, **not** a
  statement that the lane can build the kernel. Do not conflate the two.
