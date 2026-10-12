# Phase3 bootstrap: pre-existing test-tree divergence

The committed test-tree guard fails at the existing PR tip
`7d1b295296fdd5434e743268fa0e15ace57b02b9` and reviewed descendant
`c9eaef67ba89a3044d658debd655f6da7f8a28b6` with the identical offender list.
The actual scoped-delta helper reports 3155 pre-existing offenders and zero
introduced by that range. This does not make the full baseline guard green.

The complete helper-produced list is retained in
`phase3_bootstrap_preexisting_test_tree_offenders_2026-10-12.txt`, SHA256
`599b51f0edf92ecdb900dd4d55efba54ef806ff683cc98d656ebfd0308b700d6`.
Its categories include new-relative-to-baseline divergence, stale baseline and
unallowlisted mirror-only paths. Neither baseline nor allowlist was changed.

Evidence: `C:/dev/simple-phase3-bootstrap-evidence/attempt7/push-test-tree.log`
and `push-test-tree-delta.log`. The scoped exception is the explicit zero-new
offender procedure in `.claude/rules/vcs.md`; it requires recording this list.
Any later source change still requires exact-tip gate/delta validation before
push. Compiler/native validation and release admission remain separate gates.
