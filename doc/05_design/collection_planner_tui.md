<!-- codex-design -->
# Collection plan explanation output

The CLI explanation is a text surface, not an interactive UI. Its default
view must fit one screen for a single function and provide the source span,
original complexity, selected plan and why other candidates were rejected.

```text
Collection plan: orders_for_users  src/app/report.spl:42
Input: users × orders     estimated: 10k × 100k
Original: nested membership  O(users × orders)
Selected: hash semi-join    expected O(users + orders), memory O(orders)
Evidence: equality=UserId, effects=pure, order=left preserved
Alternatives: nested scan (estimated slower); merge join (inputs unsorted)
Profile: none; static estimate used
```

When no rewrite is legal, show `Selected: original` plus each missing proof,
for example `callback may mutate orders` or `duplicate policy unknown`.
`--explain-collection-plan` must have a stable machine-readable companion for
tests and tooling; source paths are displayed repo-relative. Output itself is
captured as text evidence in the mirrored SPipe manual.
