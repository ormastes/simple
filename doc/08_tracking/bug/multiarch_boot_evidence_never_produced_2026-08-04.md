# Multi-arch AC-4/AC-6 specs assert on QEMU boot evidence that no lane ever produces

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04

## Symptom

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check test/03_system/os/multiarch
# Results: 56 total, 9 passed, 47 failed
#   FAIL test/03_system/os/multiarch/six_arch_boot_spec.spl      (0 passed, 26 failed)
#   FAIL test/03_system/os/multiarch/bootstrap_pipeline_spec.spl (9 passed, 21 failed)
```

Every one of the 47 failures is the same shape: the spec calls
`file_exists("build/multiarch/<triple>/smoke_result.json")` or
`file_read("build/multiarch/<triple>/bootstrap_result.json")` and the file is
absent, so the first `it` in each `describe` fails on `false != true` and the
remaining `it`s fail reading a non-existent file.

Actual tree state:

```
build/multiarch/
└── riscv64/
    └── bootstrap_result.json     # the ONLY artifact; records "smoke_status": "fail"
```

No `smoke_result.json` exists for any of the six arches, so `six_arch_boot_spec`
is 0/26 by construction. `bootstrap_pipeline_spec`'s 9 passes are the riscv64
`describe` plus the arch-independent assertions.

## Root cause (proven)

Two independent gaps, both product-side:

1. **The per-arch bootstrap dispatch was never implemented.** The spec header of
   `test/03_system/os/multiarch/bootstrap_pipeline_spec.spl:1-9` says
   "Phase 5 adds the `--arch` dispatch" and `@cover
   scripts/bootstrap/bootstrap-from-scratch.sh`. That flag does not exist:

   ```
   $ /usr/bin/grep -n -- '--arch' scripts/bootstrap/bootstrap-from-scratch.sh
   (no output)
   ```

   There is therefore no way to run the per-arch bootstrap lane that is supposed
   to write `build/multiarch/<triple>/bootstrap_result.json`.

2. **The only writers of both artifacts sit behind a real QEMU boot.**
   `src/os/_QemuRunner/runner_targets.spl:63` defines
   `_MULTIARCH_RESULT_ROOT = "build/multiarch"`;
   `_write_smoke_result` (`runner_targets.spl:252`) and `_write_bootstrap_result`
   (`runner_targets.spl:275`) are the sole producers, and both are called from
   the `os build` / `os run` QEMU lanes after parsing serial output
   (`_smoke_result_body` takes `serial_output` and `exit_code` —
   `runner_targets.spl:223`). Nothing else in `src/` or `scripts/` writes these
   paths.

So the specs are correctly written evidence gates; the evidence pipeline
(cross-arch build + six QEMU boots) has simply never been run to completion for
five of the six arches, and cannot be run at all through the documented
`bootstrap-from-scratch.sh --arch=<triple>` entry point because that entry point
does not exist.

The single riscv64 artifact additionally records `"smoke_status": "fail"`, so
even that arch's lane last completed red — `bootstrap_pipeline_spec`'s riscv64
`post-deploy smoke is green` assertion is genuinely failing on real evidence,
not on a missing file.

## Why not fixed now

Closing this needs (a) implementing `--arch=<triple>` dispatch in
`scripts/bootstrap/bootstrap-from-scratch.sh` with the six cross toolchains and
per-arch loaders (limine / u-boot+dtb / opensbi), and (b) actually booting six
QEMU guests to capture serial evidence. This lane is explicitly forbidden from
running QEMU or booting a VM, and per `.claude/rules/board-runnable.md` the
evidence would also have to be reproducible on the physical dev board, not just
under QEMU. Fabricating the JSON files would be exactly the false-green this
gate exists to prevent.

Not fixable by editing spec or product source from a hosted test lane.

## Re-confirmed 2026-08-09

Re-checked fresh: `/usr/bin/grep -n -- '--arch' scripts/bootstrap/bootstrap-from-scratch.sh`
still returns no output (the per-arch dispatch flag still does not exist),
and `build/multiarch/` on disk still contains only the single riscv64
`bootstrap_result.json` (`smoke_status: "fail"`), no `smoke_result.json` for
any arch. Root cause and scope are unchanged from the original analysis.
Status remains **ARCHITECTURAL-OPEN**: closing this requires implementing
`--arch=<triple>` dispatch plus six real QEMU boots (and, per
`.claude/rules/board-runnable.md`, board-runnable evidence, not QEMU-only),
which is out of scope for a hosted, non-QEMU verification pass. No code
changed this pass.

## Re-confirmed 2026-08-10

Re-checked again: `--arch` still absent from `bootstrap-from-scratch.sh`
(grep exit 1), `build/multiarch/` still contains only
`riscv64/bootstrap_result.json`. Facts and scope unchanged from the
2026-08-09 pass; header `Status:` field aligned to `ARCHITECTURAL-OPEN` to
match the body (it previously said plain `OPEN`). No code change.

## Triage 2026-08-17 — LIVE in source (flag half proven)

Classified against current source, not SHA ancestry.

The `--arch` half of this report is confirmed live by content:
`test/03_system/os/multiarch/six_arch_boot_spec.spl:5` still documents the spec
as driven by `bin/simple test --arch=<triple>`, and an exhaustive
`/usr/bin/grep -rn -- --arch` over `scripts/os/` and `scripts/check/` finds the
flag ONLY in image-build scripts (`build_simpleos_install_image{,_main}.spl/.shs`,
`rebuild-sosix-qemu-media.shs`, `check-sosix-qemu-matrix.ps1`,
`check-simpleos-virtio-snd-qemu.shs`) — never in the test dispatch path the spec
calls. So the flag the spec depends on does not exist in that dispatcher.

NOT proven here: whether any lane produces the QEMU boot evidence the AC-4/AC-6
specs assert on. That needs a QEMU lane run, which was not attempted.

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: LIVE — both halves re-confirmed against current source.**

1. **The evidence is never produced.** `test/03_system/os/multiarch/six_arch_boot_spec.spl`
   asserts `file_exists("build/multiarch/<triple>/smoke_result.json")` (helper
   `_smoke_path`, line 18; first assertion line 51). `ls build/multiarch/`
   returns *No such file or directory* — the directory does not exist at all,
   so every per-arch row is asserting on a file no lane writes.

2. **The dispatch flag still does not exist.** The spec header (lines 3-5)
   states the evidence comes from running `bin/simple test --arch=<triple>`.
   `grep -rn "--arch src/app/test/ src/app/cli/` returns **zero hits** —
   the `test` command parses no `--arch` flag. The only `--arch` parsers in the
   tree belong to unrelated apps: `src/app/qemu/commands.spl:24,71`,
   `src/app/sim/profile.spl:15`, and `src/app/diagram/main.spl:230`
   (`--arch-diagram`, a different flag entirely).

So the specs are honestly RED rather than vacuously green (a missing file makes
`expect(file_exists(...)).to_equal(true)` fail), but they gate on a production
path that was never built.
