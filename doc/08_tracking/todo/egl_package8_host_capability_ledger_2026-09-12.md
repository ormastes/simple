# EGL package 8 — host-capability ledger receipt, and the fence that blocks the rest

**Date:** 2026-09-12
**Programme:** Environment-optimized dynamic Libraries (EGL), package 8
(`doc/03_plan/agent_tasks/environment_optimized_dynamic_libraries.md`, "Current package status" row 8:
*product configuration, explain receipts, packaging, guides, expert knowledge, blocked-host ledger*).
**Worktree:** `/home/yoon/dev/simple-plan-elg` @ `work/plan-elg-leftovers`, base `28a96c436b9`.
**Binary identity:** `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50,093,192 bytes, 2026-09-06 09:59:11 +0900, self-reported `Simple Language v1.0.0-rc.1`, and it
prints its own bootstrap-seed warning. Nothing below is self-hosted or admitted-native evidence.

This receipt lives here rather than in the plan's "Package 8 owner handoff" section because that plan
file is itself inside the ownership fence (see below) and is read-only for this session.

## Why most of package 8 could not be started at this base

Package 8's five documentation/product items and its implementation foundation are all held by live
Codex branches and are **absent from `origin/main` and from this base**. Verified by
`git diff --name-only origin/main...<branch>` over
`codex/egl-prod-integration-sol-20260912`, `codex/gpu-e4-e5-production-sol-20260912` and
`codex/gl-production-current-main-sol-20260912` (617 paths total):

| package 8 item | blocked by |
|---|---|
| product configuration / trusted command-config owner wiring | `src/app/cli/environment_variant_policy_sources_v1.spl`, `src/app/cli/environment_variant_policy_handoff_owner_v1.spl`, `src/app/cli/environment_variant_startup_owner_v1.spl` — fenced |
| explain receipts | needs the admission/selection types in `src/compiler/00.common/structural_contracts/environment_variant_composite_selector_v1.spl` and `src/lib/nogc_sync_mut/composition/environment_variants/**` — fenced, and not on `origin/main` |
| packaging / package integration | same foundation |
| guide | `doc/07_guide/compiler/environment_optimized_dynamic_libraries.md` — fenced |
| expert knowledge | `doc/00_llm_process/feature_expert/environment_optimized_dynamic_libraries/skill.md` — fenced |

Every one of the 17 modules and 17 unit specs under
`src/lib/nogc_sync_mut/composition/environment_variants/` and
`test/01_unit/lib/nogc_sync_mut/composition/environment_variants/` is in that fenced set and does not
exist on `origin/main`. Writing a second copy of those types here to build explain output on would
produce a shared artifact with no consumer and a guaranteed merge collision, so it was not done.

## What was delivered: the blocked-host ledger's measurement half

`scripts/audit/egl-host-capability-ledger.shs` (new, 444 lines, `sh -n` clean, executable).
It is a **probe, not a gate** — it lives under `scripts/audit/`, never blocks a push, and describes a
host rather than passing or failing a change. It needs no compiler, no self-hosted binary and no
admitted artifact, so it runs on any host in the matrix.

It emits tab-separated rows `<class>\t<id>\t<state>\t<evidence>` in four states that hand-written
prose keeps conflating:

- `present` — observable here;
- `absent` — observably not here (wrong architecture, flag missing);
- `refused` — **the thing exists but cannot be used here**, with the exact refusal text retained;
- `unprobed` — the tool that would answer is not installed, so nothing is known either way.

`refused` and `unprobed` are the reasons the script exists. Folding it into `absent` licenses the sentence "this host
has no GPU", which is false on this box, and hides that the real blocker is a permission on
`/dev/dri`.

CPU-feature rows carry the EGL feature-registry **serialized identifiers** (`0x2201` NEON, `0x2202`
SVE, `0x2203` SVE2, `0x1101`–`0x1104` x86-64 psABI levels, `0x1110`/`0x1111`/`0x1112` AVX-512
VBMI/VBMI2), so a row joins to the registry with no translation table. Vocabulary was aligned
read-only against
`codex/egl-prod-integration-sol-20260912:src/lib/nogc_sync_mut/composition/environment_variants/feature_registry_v1.spl`.
Binding to the numbers rather than the symbol names is deliberate: they are stable serialized
identities, so the rows survive that module landing, and nothing here imports a fenced module.
Feature ids are architecture-scoped in both directions — an x86 id is never emitted for a non-x86
host, so a ledger row cannot admit a variant the host could not execute one byte of.

### Red → green

Written stub-first with its eight fixture groups in place and `emit_rows` empty:

```
$ sh scripts/audit/egl-host-capability-ledger.shs --selftest
selftest: FAILED — aarch64-sve: no row matching [^cpu-feature	0x2202	present	]
exit 1
```

After implementing `emit_rows`:

```
$ sh scripts/audit/egl-host-capability-ledger.shs --selftest
selftest: PASS
exit 0
```

The selftest is fatal and runs before every real probe. Its fixtures are biting, not tautological:
an aarch64 host must not report any `0x11xx` x86 id as present; a present GPU with a refused Vulkan
device must emit **both** a `present` device row and a `refused` api row and must **not** emit an
`absent` device row; an unrecognised architecture emits an explicit `arch unknown` row and **zero**
feature rows rather than defaulting one to a baseline; and a known architecture that produced fewer
than five rows fails as vacuous.

### Measured row set for this host (2026-09-12)

```
arch	aarch64	present	aarch64
cpu-feature	0x2201	present	asimd
cpu-feature	0x2202	present	sve
cpu-feature	0x2203	present	sve2
gpu-device	nvidia	present	GPU 0: NVIDIA GB10 (UUID: GPU-1883ff9c-30a9-1b8a-bc50-ef34ac2f5a89)
gpu-api	cuda	unprobed	device enumerated; no context was created
gpu-api	vulkan	refused	failed to open device /dev/dri/renderD128
inspector-tool	llvm-readobj	present	on PATH
inspector-tool	llvm-objdump	present	on PATH
inspector-tool	readelf	present	on PATH
inspector-tool	objdump	present	on PATH
inspector-tool	clang	present	on PATH
PASS — 12 row(s) probed, 1 refused, 0 absent, 1 unprobed (arch=aarch64)
```

Two hand-written assumptions this immediately corrected:

1. **"no GPU assumed"** is wrong. The device is an NVIDIA GB10 and CUDA enumeration works; what is
   refused is the Vulkan device, on `/dev/dri/renderD128` permission. A package-6 GPU row on this
   host must say *refused, permission* — not *no device*.
2. **SVE2 is present.** It was missed by hand because a `lscpu | cut -c1-200` read truncated the
   Features line before `sve2`. So the honest aarch64 blocked fact for package 5 is not "this host
   has no SIMD"; it is that the frozen lexical primitive is an **AVX2 SysV x86-64** callable, which
   this host cannot execute regardless of its own vector width.

## What remains

- The ledger's **policy half** — joining these rows against declared variant descriptors to produce
  per-variant blocked rows with registry reason codes (`ENV_ADMISSION_*_V1`) — needs
  `environment_variant_composite_selector_v1.spl` and the `environment_variants` contracts. Both are
  fenced and absent from `origin/main`. It is a small join once that foundation lands; the row format
  above is already its input.
- Explain receipts, packaging, guide and expert-knowledge updates: blocked by the fence, not
  attempted.
- No commit, no push, no plan-file edit.

## Gates run

- `sh scripts/audit/egl-host-capability-ledger.shs --selftest` → `selftest: PASS`, exit 0.
- `sh scripts/audit/egl-host-capability-ledger.shs` → `PASS — 12 row(s) probed, 1 refused, 0 absent, 1 unprobed (arch=aarch64)`, exit 0.
- `sh -n scripts/audit/egl-host-capability-ledger.shs` → clean (POSIX sh).
- `sh scripts/check/check-guard-wiring.shs` → first run
  `FAIL — 1679 guard(s) checked, 1 NEW unwired`, naming this script. It is genuinely not a gate, so it
  was given an opt-out line with a written reason in `scripts/check/guard_wiring_optout.txt`
  (same form as the existing `profiler, not a gate` / `benchmark, not a gate` entries), not wired into
  a hook. Re-run: `PASS — 1679 guard(s) checked, 517 invoked, ..., 0 NEW unwired`.
- `git diff --no-index --check /dev/null <new file>` on both new files: exit 1 is the expected
  no-index difference for an untracked file, with **no** whitespace or error diagnostics printed.
- No C changed, so `check-c-runtime-compiles-push.shs` does not apply. No `rt_*` symbol added, so the
  dual-implementation ratchet is unaffected.

## Files

- `scripts/audit/egl-host-capability-ledger.shs` — new, 348 lines.
- `scripts/check/guard_wiring_optout.txt` — +1 line (514).
- `doc/08_tracking/todo/egl_package8_host_capability_ledger_2026-09-12.md` — this receipt.

## Three fail-opens found and closed during review (all were in the probe itself)

The first draft reproduced the defect it was written against, in its own probe functions. Each is now
closed and pinned by a selftest fixture where the fixture layer can reach it:

1. **Missing enumerator read as "no device".** With `nvidia-smi` off PATH the probe produced an empty
   string, indistinguishable from "enumerated nothing", and the row said `absent`. Now the probe
   returns a `__unprobed__` sentinel and the row says `unprobed`, naming the missing tool.
   Fixtures `gpu-unprobed`, `gpu-unprobed-not-absent`.
2. **Missing `vulkaninfo` read as a passing Vulkan.** With a GPU present and no `vulkaninfo`, the
   original emitted `gpu-api vulkan present`. Fixtures `vulkan-unprobed`,
   `vulkan-unprobed-not-present`.
3. **Enumeration reported as execution.** `nvidia-smi -L` listing a device does not prove a CUDA
   context can be created, so the CUDA row is `unprobed`, not `present`. Fixture `cuda-not-present`.

Also closed: an unreadable CPU flag list on a known architecture now ERRORs
(`lscpu` → `/proc/cpuinfo` fallback → ERROR) instead of emitting a page of silent `absent` rows, and
a failing selftest in probe mode prints its diagnostic and an `ERROR` verdict line instead of exiting
silently.

### Measured counter-example: exit codes are not sufficient evidence here

`vulkaninfo --summary` on this host **exits 0** while printing
`failed to open device /dev/dri/renderD128`, `Permission denied` and `vkCreateDevice failed`. A probe
that trusted the exit code alone would therefore report Vulkan `present` on a host where no Vulkan
device can be created. The probe reads **both** the exit code and the diagnostic text, and either
signal alone is enough to classify the device refused. Recorded because the opposite rule
("check the exit code, not error strings") is the usual advice and is wrong for this tool.

## Known limits, stated rather than assumed

- CPU flags are the **union** across core models. This host is heterogeneous (Cortex-X925 +
  Cortex-A725) and the two flag sets happen to match, but on a big.LITTLE host where only the big
  cores carry a feature this would report it present while a migrated thread would fault. Intersect
  per `Flags:` line before trusting the ledger on an asymmetric host.
- The psABI level ↔ `ENV_FEATURE_X86_64_V{2,3,4}` mapping is **inferred** from the registry constant
  names. `feature_registry_v1.spl` defines bit masks, not CPUID flag sets, so that correspondence
  must be confirmed by the registry owner before an x86 row is used for admission.
- The probe proves what the host reports, not that any variant
  executes. No row here is admitted-native or self-hosted evidence.
