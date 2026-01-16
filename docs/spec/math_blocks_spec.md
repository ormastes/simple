*Source: `simple/test/system/features/math_blocks/math_blocks_spec.spl`*
*Last Updated: 2026-01-16*

---

# Math Block Tensor Operations Specification

**Feature IDs:** #1090-1098 (subset: tensor ops)
**Category:** Syntax / Math DSL
**Difficulty:** 4/5
**Status:** Implemented

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

Basic arithmetic operations.

Built-in math functions.

Matrix operations that produce scalar results.

Built-in math constants.

Array expressions that produce scalar results through reductions.

LaTeX-style syntax support (with deprecation warnings).

Math expressions can be exported to LaTeX format.
