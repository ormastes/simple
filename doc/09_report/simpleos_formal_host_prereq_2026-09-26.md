# SimpleOS formal host prerequisite evidence (2026-09-26)

This is a host toolchain receipt for the SimpleOS mission-critical release
prerequisite. It is **not** a SimpleOS proof result, immutable-candidate
qualification, or release admission.

## Host and exact tools

- Host: Darwin arm64; source checkout: `e865f106bb3`.
- Yosys: Homebrew `0.69+post`, built from `143eb14f9cc55d6f8927e68523b0c9d2166ed02c`.
- SymbiYosys: `YosysHQ/sby` commit `b1a1e98cba941ec8433f8dc27f416cd7bb7f14be`, installed under the ignored `build/simpleos_formal_tools/sby-install` prefix. Its `sby --version` prints `SBY` because the shallow checkout has no release tag.
- Python dependency: `click 8.5.0` in the prefix's `pydeps` directory.
- SMT solver: Homebrew Z3 5.1.0.

With `PATH` including `build/simpleos_formal_tools/sby-install/bin` and
`PYTHONPATH` including its `pydeps` directory,
`sh scripts/check/check-simpleos-mission-critical-prereqs.shs` returned
`STATUS: PASS`, `status=ready`, `missing=none`, and `next_action=none`.

An independent one-step combinational assertion in the ignored
`build/simpleos_formal_tools/smoke/proof.sby` ran through SBY, Yosys, and Z3.
Its log ends `DONE (PASS, rc=0)` and reports successful k-induction. This only
shows that the installed toolchain can run a small proof; it does not prove
any product RTL.

The smoke fixture was `module proof(input wire a); always @* assert(a == a);
endmodule` with SBY `mode prove`, `depth 1`, engine `smtbmc z3`, and script
`read -formal proof.v; prep -top proof`. It was run from the fixture directory
with `sby -f proof.sby`; the complete local log is
`build/simpleos_formal_tools/smoke/run.log`.

## Remaining release gates

- The RISC-V product SBY gate first calls the FPGA sidecar contract, which
  requires an admitted self-hosted Simple compiler to generate the RTL.
  Automatic compiler selection found no admitted runner in this checkout.
- The macOS from-scratch bootstrap still stops at the Cocoa runtime ownership
  gate. Its proposed fix is dirty in a separate shared worktree and was not
  copied into this lane.
- The full SimpleOS hardening matrix and mission-critical release gate were
  not rerun here. The existing matrix self-test uses fake ready fixtures and
  does not qualify a release.

Once a source-matched pure-Simple runner is available, run the product proof
and full release matrix with the formal-tool environment above. Keep proof
artifacts and the matrix report bound to that exact source and compiler.
