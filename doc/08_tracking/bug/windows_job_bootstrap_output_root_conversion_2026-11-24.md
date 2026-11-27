# Windows Job handoff converts the bootstrap output allowlist

The MSYS Perl watchdog launches a native Windows Job supervisor, which starts
an MSYS shell workload. MSYS converts path-valued environment variables at
the native boundary. `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT=/c/...` therefore
arrived in the shell as `C:/...`. The bootstrap authority requires a canonical
POSIX absolute root and correctly refused it with
`bootstrap-output-outside-allowlisted-root` (exit 64 in the real planner).

All in-tree readers of this variable are bootstrap/check shell scripts. The
watchdog already preserves its shell-owned helper-cache variable across this
boundary. Extend that exact-name exemption to the external output root while
preserving existing caller exclusions. Do not normalize arbitrary authority
inputs, broaden the allowlist, or disable general native path conversion.

The real Windows Job regression is:

```text
python scripts/bootstrap/tests/windows-output-root-env-test.py --cc C:/msys64/ucrt64/bin/clang.exe --output-root <fresh-external-evidence-directory>
```

On the release baseline, the captured inherited root was `D:/.../external`
and the test failed. With the repair, the same production authority accepts
the exact external root and refuses an existing directory outside it. The
test also launches a real native Python child: unrelated environment and argv
paths still convert to Windows form; caller and helper-cache exemptions remain
present exactly once. The Job receipt reports complete/exit 0, quiescent and
RSS enforcement at 256 MiB. No compiler or bootstrap stage is executed.

Session evidence is retained under
`release-bootstrap-20261123/evidence/output-root-env-baseline` and
`output-root-env-after`. An earlier harness launch lacked `/usr/bin` in PATH
and stopped at `cygpath` before reaching the owner; it is not the baseline
reproduction. The regression now selects the MSYS utility path explicitly.
