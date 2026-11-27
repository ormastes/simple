# Focused HIR closure admission

Status: AUTHORED / NOT_RUN. No compiler or native worker execution in this lane.

The executable controls call the existing production closure-count helper. They
check zero/one workers, default threshold and its boundary, memory ceilings,
20/80/128 requested capacity, explicit zero threshold and unknown closure size.
A separate wiring guard targets the focused route's unique call expression.
These controls do not prove actual process count, output parity or performance.

Finite runtime plan (runtime owner only): run this spec once with the admitted
full CLI. Then one published one-file closure with file-worker mode disabled,
request20 and the default threshold must start zero HIR warming workers; with
threshold0 the helper admits one and the focused route's existing >1 gate keeps
it in process. A five-file closure/request20 admits at most5; a memory-admitted
ceiling3 stays at most3. Check exact output, claim completeness and no successful
row for failed work. Unknown closure size retains the existing requested count.
Use one bounded fixture build per case, timeout120s, isolated cache/output, and
retain the runtime identity, selected closure count, launch count and log.
No large bootstrap or repeated green matrix is authorized by this test plan.
