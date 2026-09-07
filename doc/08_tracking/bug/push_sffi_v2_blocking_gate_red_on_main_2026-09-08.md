# Blocking SFFI v2 push gate was knowingly red on main

## Symptom

An unrelated SciLib topic could not be pushed because four SFFI authority
children already failed on its current mainline parent. The manifest described
the blocking gate itself as honestly red.

## Fix

Push dispatch now supplies the committed outgoing base. The aggregate records
failed child-guard identities for base and tip, admits unchanged or reduced
failure sets, and rejects every newly failing guard. Ordinary runs still
require all 46 children to pass.

## Evidence

Five selftest fixtures cover committed-tree isolation, absent guards,
unchanged-red admission, and newly-red rejection.
