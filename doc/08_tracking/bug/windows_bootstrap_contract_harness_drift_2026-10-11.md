# Windows bootstrap contract harness drift

Status: FIXED in candidate; focused Windows host checks passed. Full bootstrap
and Phase4 admission remain separate, unfinished qualification.

Source baseline: release_phase3 0c7bb72f83663c4407e694af1388109be25d7ac3.
Two existing wrapper checks failed before exercising their intended boundaries:

- `check-bootstrap-windows-authority-paths.shs` extracted only the Cargo wrapper
  after production split environment handling into `run_rust_authority_command`.
  It also omitted `PLATFORM_RUST_TRIPLE`, producing an unbound-variable failure.
- `check-bootstrap-path-access.py` hardcoded Git Bash under Program Files. This
  host installs Git at `C:/dev/tool/Git`, so process creation failed with WinError 2.

The authority fixture now extracts both actual production functions, binds the
Rust target, and verifies exact Cargo arguments as well as TEMP/TMP/SystemRoot
across all four LLVM/LTO branches. No compiler or Cargo build is substituted.
The PATH fixture discovers Git Bash beside Git on Windows, permits an explicit
`--shell` for MSYS2/custom installations, and uses PATH Bash on POSIX. Windows
ambient Bash is not selected automatically because it can be the WSL launcher.

Evidence lives in `build/windows-phase4-logs/agent-contracts/`: original failures
in `authority-paths.log` and `path-access.log`; corrected-copy validation in
`authority-fixed.log`, `path-fixed.log`, and `shell-selection.log`. Source copies
were validated without altering the live bootstrap source while it was frozen.
The PATH behavior matrix executed 10 cases with 10 passes; selection probes
covered explicit paths with spaces, missing native Bash, and POSIX discovery.
The authority check passed four root aliases, four Cargo branches, missing-root
rejection, and three target suffix layouts. The independent toolchain contract
also passed 3 accepted/6 rejected LLVM versions and 5 executable-selection cases.

Reproduction after applying the repair:

```sh
sh scripts/check/check-bootstrap-windows-authority-paths.shs
python scripts/check/check-bootstrap-path-access.py \
  --script scripts/bootstrap/bootstrap-from-scratch.sh \
  --output build/windows-path-contract-fresh
```

Use a new private output directory; the PATH fixture refuses existing outputs.
These harness results do not establish successful compiler bootstrap or native
Windows Phase4 qualification.
