import Lake
open Lake DSL

package tensor_dimensions where
  srcDir := "src"

@[default_target]
lean_lib TensorDimensions

@[default_target]
lean_lib TensorMemory
