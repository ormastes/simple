# Bounded directory facade controls

Status: **AUTHORED / NOT_RUN**. No admitted Simple CLI was used.

The adjacent spec checks real empty-directory EOF, a regular file and its size,
missing-path probe versus missing listing failure, exact entry/name budgets and
hard-cap rejection. It cleans its files before assertions. Native C evidence is
separate: `scripts/check/check-directory-bounded-v1.shs` exercises the shared
provider with real POSIX filesystem operations and tagged-text test handles.

Native evidence does not qualify Simple code generation, the Rust interpreter,
Windows, or hosts not actually executed.
