import Lake
open Lake DSL

package visibility_export where
  srcDir := "src"

@[default_target]
lean_lib VisibilityExport
