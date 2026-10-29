# Resume a rejected Stage 2 build from its native cache

Run `sh scripts/bootstrap/resume-stage2-from-cache.sh /absolute/worktree/build/prior-output`
in the same host environment after the previous bootstrap releases its output
lock. The wrapper validates the retained command and frozen runtime, copies
content-addressed cache files into a fresh output, and delegates to the canonical
bootstrap. Old rejected binaries and sanity/admission evidence stay behind.

Windows MSVC and GNU use `simple.exe` for canonical Stage 2 output, private
admitted output and the frozen runtime compiler. Linux and Darwin use `simple`.
The host triple determines the suffix; an alternate transcript spelling is
rejected. Do not edit transcripts or rename rejected candidates to bypass this
validation. Existing canonical or admitted binaries also prevent cache resume.

The wrapper's successful validation is not compiler qualification. The new
bootstrap must complete its unchanged sanity, receiver and admission checks.
Resource-policy or compiler failures need their own diagnosis and retained
evidence before another isolated attempt.

Run `sh scripts/check/check-bootstrap-stage2-resume-platform.shs` for the bounded
platform-path regression (24 cases, no compiler or admission execution).
