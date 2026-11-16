# Input-profile DATA comparison

Status: AUTHORED_NOT_RUN. Uses the real production pure checker with deliberately
synthetic DATA; no DTO is admitted as actual provider or Host evidence.

1. Matching base plus OpenStdin=false/Tty=false must compare successfully. Changing
   observational StdinOnce alone must not invent an EOF requirement.
2. Open stdin or TTY must refuse. Changed exact runtime or request digest must
   fail through the existing base checker; invalid outer digest shape must refuse.
3. Copy the production input restriction, mutate the original nested argv/mounts,
   and require retained fields/profile to stay unchanged.

Absent/nonboolean native input fields and bracketing changes belong to the actual
query producer's specs. Native admission, actual closed input, child EOF, prompt
delivery and task completion are NOT_COVERED by these DATA assertions.
