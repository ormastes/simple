# Provisional startup drops requested resource policy

Status: launcher routing verified; end-to-end bootstrap validation pending.

The provisional Phase 3/4 launcher accepts `--lifetime-ms=0` and `--memory-policy=monitor`, but its hello compile previously always used a 600-second timeout and enforced RSS containment. Both manager-image preparation calls also omitted the selected threads, timeout, and memory policy, reverting to helper defaults before managed work could start.

The repair forwards the selected policy to hello compilation and both image preparation calls. Milliseconds are rounded upward to seconds; zero remains unlimited. The hello helper retains its standalone defaults of 600 seconds and enforced RSS, validates explicit overrides, and uses the requested memory policy during compile and execution. The tiny hello executable retains its separate 30-second execution check. Source, producer, receipt, output, and host-capacity validation remain required.

Shell syntax and whitespace checks passed. Six option-validation cases passed: zero/monitor and positive/enforce reach required-input validation; negative, leading-zero, nonnumeric timeout and unknown memory policy are rejected. This only verifies option parsing, not producer execution or manager dispatch. Evidence: C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/provisional-startup-policy-validation.json.

The production startup-call spy test passes for all three pre-ready invocations, including millisecond rounding at 0, 1, 1000, and 1001. The existing final-dispatch policy test and changed-hello-source refusal test also pass. Working and staged environment guards pass; tracked executable specs under doc/06_spec count zero. These establish the script forwarding behavior, not a completed Phase 3/4 bootstrap.

The active PR2385 compiler builds use unchanged source. Use this launcher repair when a usable compiler becomes available; do not claim Phase 3/4 admission from these checks.
