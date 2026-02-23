import Lake
open Lake DSL

package «borrow_checker_safety» where
  version := v!"0.1.0"

@[default_target]
lean_lib BorrowCheckerSafety where
  roots := #[`BorrowCheckerSafety]
