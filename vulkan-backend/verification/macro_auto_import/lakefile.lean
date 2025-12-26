import Lake
open Lake DSL

package macro_auto_import where
  srcDir := "src"

@[default_target]
lean_lib MacroAutoImport
