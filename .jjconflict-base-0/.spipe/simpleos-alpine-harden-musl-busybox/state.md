# SStack State: simpleos-alpine-harden-musl-busybox

## Raw Request
> harden simple os from alpine, check std lib of simple os, let it follow musl libc like
> refctor current to simple full featured. busybox like tool refactor existing(check missing,
> make it simple like busybox but keep mdsoc+). pie ssp relro config for simple desktop os
> default config for embedded configurable. make them in pure simple if perf or hw access
> problem happen add to perf bug or feature lag bug. and fix them. and simple to support
> simple os host like win, linux, mac and bsd. handle simple os as same way like other hosts
> with few optimization for simple os since it share same features.

## Task Type
feature (multi-pillar, multi-session)

## Refined Goal
> Bring SimpleOS to Alpine-Linux-class hardening posture: (P1) capability exec gate + hardened
> malloc; (P2) refactor `src/os/libc` from C into pure-Simple, musl-shaped, full-featured libc;
> (P3) busybox-style argv[0] multi-call dispatcher over existing applets + missing applets, keep
> MDSOC+; (P4) PIE/SSP/RELRO as per-`TargetPreset` policy (desktop ON, embedded configurable) +
> SSP codegen; (P5) register SimpleOS as a first-class compiler HOST alongside linux/macos/win/bsd.

## Acceptance Criteria
### P1 — Alpine-class hardening
- AC-1: DEFERRED to open `simpleos-harden-exec` lane (it owns the capability exec gate on
  `fs_exec_spawn`). This lane links to it; no double-editing.
- AC-2: pure-Simple hardened malloc (guard pages/canary/slabs), selectable; spec traps double-free.
  [OPEN — needs mmap, sequential]
### P2 — musl-shaped pure-Simple libc
- AC-3: pure-Simple string/ctype/stdlib core vs musl outputs. [DONE — string+stdlib slices green]
- AC-4: pure-Simple musl-style buffered stdio (FILE*/fread/fwrite/fgets/fflush). [DONE — FileBuf green]
- AC-5: port remaining pure-computation C libc → pure Simple. [DONE for string/mem/stdlib-integer:
  +simpleos_string_copy.spl (strcpy/strncpy/strcat/strncat/strdup/strndup/strnlen/strlcpy/strlcat, 30/0)
  +simpleos_string_search.spl (strstr/strspn/strcspn/strpbrk/memchr/memrchr/strcasecmp/strncasecmp/
  strtok_r/strerror, 51/0) +simpleos_stdlib_num.spl (strtoul/strtoll/strtoull/div/ldiv/lldiv/rand,
  41/0) — 26 fns, 122 examples, all pure (no extern/rt_/C). C twins kept until parity.
  REMAINDER BLOCKED & FILED: float (strtod/strtof/math/printf_float) needs reliable f64; syscall group
  (alloc/fs/fork/signal/pthread/time/…) is legitimately C — `simpleos_libc_float_port_blocked_f64_2026-06-28.md`.
  Opus-review follow-up (2026-06-28): added strlcpy/strlcat (BSD, were dropped) via LcResult{bytes,total};
  fixed strtoul to accept leading +/- sign (C-conformant, was diverging); strtok (non-reentrant, static
  state) DELIBERATELY superseded by reentrant strtok_r — not ported (decision recorded, not silent skip).]
### P3 — busybox multi-call (keep MDSOC+)
- AC-6: `simplebox` argv[0]/argv[1] dispatch over registry + `--list`, MDSOC+ annotated. [DONE — green]
- AC-7: missing applets (dd/chown/timeout/+) pure-Simple + registered. [DONE — cores green]
- AC-6b: WIRE userland→image. [DONE — simplebox_main.spl entry genuinely consumes pure-Simple libc
  (seq via libc_strtoul, 8/0); simplebox_build.spl native-build→rootfs (5/0); image_builder packs
  /bin/simplebox into the rootfs + deploy manifest (proven by image_builder_artifact_spec block 1).
  Pre-existing nvfs-marker failure in that spec's block 3 filed (image_builder_nvfs_rootfs_marker_
  preexisting_2026-06-28.md) — NOT caused by this wire (origin fails it identically).
  SYSROOT BUILT FOR REAL (sh src/os/port/llvm/sysroot.shs): libsimpleos_c.a 137KB + crt0.o + simpleos.ld
  + headers under build/os/sysroot (gitignored). simplebox_build.spl = canonical invocation
  (--backend llvm/--source src/os+src/lib/--entry-closure/--target x86_64-unknown-none/
  --linker-script), 7/0 (dropped a no-op --timeout assertion: the 120s deaths were Simple's own
  process_run_timeout default, not native-build).
  ROOT-CAUSED the cross-compile blocker (was mis-filed as "no emit"). Three symptoms, none "no emit":
  (1) 120s death = process_run_timeout default (test harness); (2) ld.lld cannot open
  simple_rt_runtime.o = STALE deployed bin/simple seed (current cargo seed builds single libc module
  -> real freestanding PIE ELF); (3) THE WALL = const-eval `cannot parse 'c' as i64`: native-build
  parses hex literals digit-by-digit via int(hc), and int("c") numeric-parses->fails, so ANY hex
  literal with an a-f digit (e.g. kernel 0xc... LIMINE consts scanned by --source src/os) aborted.
  FIXED in primary_expr.spl (lookup-string hex map, no int(letter)); verified 0xca=202/0xDEAD=57005/
  0b1010=10; regression spec hex_literal_const_eval_spec.spl 7/0. Lane libc EXONERATED (marker test:
  renaming ["c",...]->["zzcmark",...] kept identical 'c' error). With hex fixed, native-build still
  can't emit a typed/module integer val (`val x:i64=255`->"unwrap on Type"; module `val M:i64=0xca`->
  "kind on nil") — SEPARATE pre-existing gaps, now the remaining blocker (Part 2 of the bug doc).
  Bug doc: native_build_const_eval_int_letter_2026-06-28.md. Image pack uses placeholder until Part 2.]
### P4 — PIE/SSP/RELRO policy
- AC-8: desktop/Hosted hardening stays UNCONDITIONALLY ON (no regression); ADD embedded opt-out via
  preset. [DONE — resolve_hardening + regression-guarded spec green]
- AC-9: SSP codegen (clang `-fstack-protector-strong` + LLVM IR `sspstrong`). [OPEN — filed as bug]
- AC-10: spec asserts desktop links `-pie -z relro -z now` (+canary when SSP lands); embedded opts
  out. [PARTIAL — config policy green; link-flag assertion pending build]
### P5 — SimpleOS as compiler HOST
- AC-11: `cfg_normalize_os("simpleos")` + `@cfg(os="simpleos")` parse + platform_defaults unix-like.
  [DONE — cfg+attr branches green, linux/freebsd regression-guarded]
- AC-12: linker treats "simpleos" unix-like; link-plan spec. [DONE — platform_defaults simpleos
  host branches (libs/crt/loader), proven populated-vs-empty-fallback, linux/freebsd regression-
  guarded, 12/0]. host_os() runtime-detection string is the runtime's job on real SimpleOS (not
  needed for cross-link); port of remaining C libc postponed (keep C until parity per user).
### P6 — Docs & tracking
- AC-13: new sspec SYSTEM tests follow `qemu_systest_contract` fail-closed + listed in guide. [DONE]
- AC-14: deferred perf/hw items filed as concrete bugs, no silent TODO/NOTE. [DONE — 3 bugs filed]

## sspec System Test Cases (deliverable — authored, fail-closed)
- `test/03_system/os/qemu/os/harden/cap_exec_gate_spec.spl` — AC-1
- `test/03_system/os/qemu/os/harden/hardened_malloc_spec.spl` — AC-2
- `test/03_system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl` — AC-8/9/10
Each = media-check `it` (`rt_file_exists` kernel+image) + boot `it`
(`run_qemu_systest(...) == SYSTEST_PASS`), NO `skip()`. RED (missing-media) until the harden probe
build target lands (filed: `doc/08_tracking/bug/simpleos_harden_probe_build_target_2026-06-28.md`).

## Modules landed (pure Simple, interpreter-verified)
- `src/os/libc/simpleos_string.spl` (+ `test/01_unit/os/libc/libc_string_ctype_spec.spl`) — 14/0
- `src/os/libc/simpleos_stdlib.spl` (+ `…/libc_stdlib_spec.spl`) — atol/abs/labs/max/min/bsearch/qsort
- `src/os/libc/simpleos_stdio.spl` (+ `…/libc_stdio_spec.spl`) — FileBuf buffered stdio — 13/0
- `src/os/tools/simplebox/simplebox_dispatch.spl` (+ `…/simplebox_dispatch_spec.spl`) — 25/0
- `src/os/tools/simplebox/simplebox_applets_core.spl` (+ `…/simplebox_applets_core_spec.spl`) — 16/0
- (libc_stdlib spec = 38/0 after un-hollow fix)
- **Verified tally: 123 real passing unit examples (authored_it == reported), 0 failures
  (interpreter) — after fixing 3 hollow specs (sibling top-level describes only ran the last group).**
- `src/compiler/{10.frontend/core/cfg_platform.spl,30.types/platform_attr_parser.spl}` +simpleos
  (+ `test/01_unit/compiler/simpleos_host_cfg_spec.spl`) — 5/0, linux/freebsd regression-guarded
- `src/compiler/70.backend/linker/platform_defaults.spl` — `ssp` field + `HardeningPolicy` +
  `resolve_hardening` (+ `test/01_unit/compiler/hardening_preset_policy_spec.spl`) — 12/0
- `src/os/qemu_systest_contract.spl` — harden_* helpers + 3 marker lists

## Bugs filed (AC-14)
- `doc/08_tracking/bug/simpleos_ssp_codegen_feature_lag_2026-06-28.md`
- `doc/08_tracking/bug/u8_index_generics_deprecation_false_positive_test_path_2026-06-28.md`
- `doc/08_tracking/bug/simpleos_harden_probe_build_target_2026-06-28.md`
- `doc/08_tracking/bug/spec_runner_drops_sibling_top_level_describe_2026-06-28.md` (hollow-green trap)

## Honesty notes (Opus review)
- libc/applet modules are NOT yet wired in (don't replace the C libc, no simplebox entrypoint) —
  foundation logic, interpreter-verified, not live behavior. Codegen verification pending (JIT rt_len
  gap). `resolve_hardening` is computed but linker_wrapper/mold are unchanged — policy landed, NOT yet
  consumed by the link path (that wiring is follow-up).
- Durable: pushed to origin/main (tip e42ace4). Recovered twice from parallel-session WC clobbers.

## Cooperative Review
- Sidecars: Haiku (mechanical: libc fns, applets, stdio), Sonnet (design: dispatcher, host-cfg,
  hardening policy, system tests). Merge owner: main session. Final reviewer: Opus (advisor) — 2
  passes done; corrections applied (RELRO no-regress, AC-1 defer, interpreter-vs-codegen honesty).

## Scope Exclusions
- No GUI/desktop-shell work. No new external deps (pure Simple; Rust seed untouched).
- Not all ~30 libc .c files in one pass (AC-5 tracks remainder). No full musl test-suite parity.

## Phase
implement-in-progress (8 modules green; system tests authored; AC-2/5/9/12 open)

## Log
- dev: state file, 14 ACs across 6 pillars.
- research: 5 parallel sonnet agents mapped libc/busybox/hardening/host/alpine.
- arch/spec: Opus review — defer AC-1, keep desktop RELRO always-on, run spec before scaling.
- implement b1: libc string slice green (14/0); SSP-codegen + [u8]-lint bugs filed.
- implement b2 (parallel haiku/sonnet): libc stdlib + stdio, simplebox dispatch + applets, host cfg,
  hardening preset policy — all green; 3 fail-closed QEMU SYSTEM specs authored; harden-build bug.
- RECOVERY 2026-06-28: a parallel-session jj reconcile clobbered uncommitted batch-1 files + lane
  dir; recreated from context and COMMITTED IMMEDIATELY (lesson: commit after every edit under churn,
  per .claude/rules/vcs.md). Re-verified content after recreate.
