# Stage4 atomic-database HIR names

## Reproduction

Stage4 HIR lowering stopped in `nogc_async_mut/db_atomic.spl` with unresolved
file, lock, process, time, and `_` names.

## Fix

Both no-GC database mirrors import file operations, process identity, and time
from their concrete owner modules. The async mirror now uses the same `?`
Result propagation as the sync implementation instead of matching `Ok(_)`,
which Stage4 treated as an unresolved identifier.

## Regression evidence

`db_atomic_hir_contract_spec.spl` checks concrete owners, removal of the broad
facade import, native-safe propagation, and sync/async mirror parity.
