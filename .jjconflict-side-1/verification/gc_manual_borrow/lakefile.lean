import Lake
open Lake DSL

package gc_manual_borrow where
  srcDir := "src"

@[default_target]
lean_lib GcManualBorrow
