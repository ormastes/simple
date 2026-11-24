# Conditional canonical Linux continuation (stage only)

Consumes only successful P3a run45340259012/control9c1de732 with the unchanged reviewed phase3-parent.py gate. No P3a rerun or extra parent Hello. Frozen compiled source656fa39e is separate from landed wrappered9c404d.

P3b uses --phase=p3b, actual --p3a-bin and exact SHA, fresh output/cache, and canonical native Hello. Only successful P3b publishes the sealed handoff.tar; a separate P4 runner verifies actual same-run artifact identity, owner, source/runtime/wrapper, ELF and native Hello before --phase=p4. Tar preserves file modes; only regular files are permitted. No old cache or queue is installed. Both jobs use measured75% availability/2GiB reserve and finite owners; native admission estimates remain unchanged.

P4 retains canonical src/app/cli/main.spl, release/debug CLI and four essentials, unchanged CUDA choice. Existing full CLI run/positive/negative/native Hello qualification executes the actual canonical release bin/simple, with its own smoke cache; no second CLI compilation. The earlier armed P3a-derived direct CLI remains a distinct generation result.

No formal scheduler admission, deployment or publication. Observer3024 and its control remain unchanged. This workflow is not dispatched or automatically armed. Parent success, final review and a single coordinated dispatch remain prerequisites. It must not be retried automatically after ambiguous submission.
