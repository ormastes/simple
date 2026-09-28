# Target 6 exact untracked-stage query

The warm inventory bridge previously ran `git ls-files --cached` over all
selected source roots whenever an untracked source disappeared from Git's
untracked listing. It then built a tracked-path map solely to distinguish a
staged file from a deleted file. The candidate asks Git only for the former
untracked paths, using `:(literal)` pathspecs so glob characters in a source
name cannot change that decision. A matching result must be one of the queried
paths; otherwise refresh fails closed. No-op warm requests do not enter this
branch, so this change makes no no-op latency claim.

The integration fixture adds a `src/[a].spl` untracked-to-staged transition
and asserts that the source remains in the admitted inventory. The no-stub
native binary built from 97 entry-closure units at 240 KiB. Its textual verdict
was **1 example, 1 failure**. Diagnostic output located the failure at the
fixture's initial cold refresh: `observed-event-apply:event-invalid`, before
the new stage-transition branch runs. `git add -- :(literal)src/[a].spl`
itself returned zero. The older Stage2 cold-replay defect is already noted in
the persistent-index plan. The three-cycle fixture limit was reached, so the
candidate has no passing native correctness or paired performance receipt.

Next: run the fixture with a newly admitted pure-Simple compiler that can
publish the cold inventory, then measure the staged-transition workload's
time and peak RSS against the same fixture before the query change. Keep the
Target 6 PR draft until those results and the broader index cutover pass.
