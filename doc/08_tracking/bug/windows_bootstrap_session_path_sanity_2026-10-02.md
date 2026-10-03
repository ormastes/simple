# Windows bootstrap sanity session-path refusal

Status: focused regression PASS; retained compiler remains unqualified.

The canonical build of source `7734f947be8ba9465d0ba312170681074e990587`
linked 1,136 modules, then rejected Stage 2 without any advertised sanity
logs. Its outer Job completed with exit 1 and `quiescent=1`; neither the
memory cap nor disk floor caused the stop. Missing logs alone do not prove
whether the retained compiler was invoked in that original run.

The reproduced failure is the native boundary in
`scripts/check/lib/portable-session-exec.pl`: MSYS converts the exported
`SIMPLE_BOOTSTRAP_SESSION_EXEC` from `/d/...` to `D:/...` when executing
`bootstrap-session-exec.exe`. That native helper starts an MSYS shell with
the converted environment. The shell sanity gate requires a POSIX absolute
helper path and silently returns 125 before any evidence log is initialized.

The wrapper now excludes precisely `SIMPLE_BOOTSTRAP_SESSION_EXEC=` from
MSYS environment conversion, preserving existing exclusions. The change is
limited to MSYS/Cygwin; the POSIX execution path is unchanged. Both fresh
and resumed sanity gates now report typed reasons for session validation
refusals and preserve/report the frontend capture setup's failing status.
Session membership validation and all admission requirements remain intact.

## Bounded evidence

Local evidence root: `D:/dev/windows-sanity-gate-evidence-20261002`.
Every attempt used the existing native session helper with SHA-256
`9b336f5d423521dc44518ebd8c96e1d26af64867890a6dde5839730c76408819`,
a 10-second timeout, a 131,072-KiB RSS cap and 100-ms observations.
Each attempt received a fresh physical/commit admission with an additional
8-GiB reserve and a physical-D floor of 9,126,805,504 bytes. No attempt
compiled or executed a Simple candidate. No build cache was changed.

| Cycle | Result | Peak RSS KiB | Terminal state |
|---|---|---:|---|
| 1 | Unchanged direct gate prefix returned 0. Fixture could not locate Perl; wrapped case did not run. | 27,492 | complete / exit 127 / quiescent 1 |
| 2 | Shipped portable wrapper produced `D:/...`; unchanged gate prefix returned 125. | 39,964 | complete / exit 0 / quiescent 1 |
| 3 | Fixed native wrapper retained `/d/...`; real helper membership check passed and existing exclusions survived. | 60,312 | complete / exit 0 / quiescent 1 |

Cycle 3 ran `scripts/check/check-windows-sanity-session-path.shs` inside
the real Job. It extracted both production gate functions and verified
four session refusal reasons (status 125) plus a frontend capture refusal
(status 126). Synthetic stop collaborators prevent candidate execution;
these checks establish wrapper and diagnostic behavior, not frontend or
compiler correctness. Shell/Perl syntax and whitespace checks passed.
Three cycles are complete; no unchanged passing check was rerun.

The frozen source and `simple.exe.rejected` were preserved. A separately
reviewed diagnostic replay or canonical admission remains necessary before
the retained binary can qualify for subsequent bootstrap stages.
