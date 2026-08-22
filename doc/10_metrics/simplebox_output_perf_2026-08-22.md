# SimpleBox output performance evidence — 2026-08-22

| Path | Before | After | Auxiliary memory | Bound |
|---|---|---|---|---|
| `echo` | O(n²) growing-prefix copies | O(n) part scan + one join | O(a) text references plus n-byte result, where a is argument/separator count | 65,536 output bytes |
| `seq` | O(count), unbounded | O(min(input, 64) + output bytes) preflight + emission | O(1) | 65,536 output bytes; at most 12,773 values |

The allocation proxy is the actual `SimpleboxEchoPlan.parts` length: four
one-byte arguments retain eight pieces (four arguments, three separators, one
newline), rather than allocating a new full prefix for every append. Seq's
operation proxy records inspected input bytes and values; an oversized decimal
is rejected before output planning, while the largest accepted count is 12,773
(65,532 output bytes).

No wall-time/RSS row is claimed: the required pure-Simple runtime and optimizer
are absent from this worktree. Run the focused specs and
`bin/simple run src/app/optimize/main.spl <touched-file> --full --level=O3` once
an admitted self-hosted binary is installed; do not substitute the Rust seed.
