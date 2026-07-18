# Symbol Kind Specification

> <details>

<!-- sdn-diagram:id=symbol_kind_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbol_kind_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbol_kind_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbol_kind_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 80 | 80 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Kind Specification

## Scenarios

### SymbolKind to_string

#### converts File to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case File: "file"
val kind = "file"
assert_true(kind == "file")
```

</details>

#### converts Module to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Module: "module"
val kind = "module"
assert_true(kind == "module")
```

</details>

#### converts Namespace to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Namespace: "namespace"
val kind = "namespace"
assert_true(kind == "namespace")
```

</details>

#### converts Package to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Package: "package"
val kind = "package"
assert_true(kind == "package")
```

</details>

#### converts Class to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: "class"
val kind = "class"
assert_true(kind == "class")
```

</details>

#### converts Method to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Method: "method"
val kind = "method"
assert_true(kind == "method")
```

</details>

#### converts Property to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Property: "property"
val kind = "property"
assert_true(kind == "property")
```

</details>

#### converts Field to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Field: "field"
val kind = "field"
assert_true(kind == "field")
```

</details>

#### converts Constructor to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constructor: "constructor"
val kind = "constructor"
assert_true(kind == "constructor")
```

</details>

#### converts Enum to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: "enum"
val kind = "enum"
assert_true(kind == "enum")
```

</details>

#### converts Interface to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: "interface"
val kind = "interface"
assert_true(kind == "interface")
```

</details>

#### converts Function to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Function: "function"
val kind = "function"
assert_true(kind == "function")
```

</details>

#### converts Variable to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Variable: "variable"
val kind = "variable"
assert_true(kind == "variable")
```

</details>

#### converts Constant to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constant: "constant"
val kind = "constant"
assert_true(kind == "constant")
```

</details>

#### converts text to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case text: "string"
val kind = "string"
assert_true(kind == "string")
```

</details>

#### converts Number to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Number: "number"
val kind = "number"
assert_true(kind == "number")
```

</details>

#### converts Boolean to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Boolean: "boolean"
val kind = "boolean"
assert_true(kind == "boolean")
```

</details>

#### converts Array to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Array: "array"
val kind = "array"
assert_true(kind == "array")
```

</details>

#### converts Object to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Object: "object"
val kind = "object"
assert_true(kind == "object")
```

</details>

#### converts Key to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Key: "key"
val kind = "key"
assert_true(kind == "key")
```

</details>

#### converts Null to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Null: "null"
val kind = "null"
assert_true(kind == "null")
```

</details>

#### converts EnumMember to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case EnumMember: "enum-member"
val kind = "enum-member"
assert_true(kind == "enum-member")
```

</details>

#### converts Struct to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: "struct"
val kind = "struct"
assert_true(kind == "struct")
```

</details>

#### converts Event to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Event: "event"
val kind = "event"
assert_true(kind == "event")
```

</details>

#### converts Operator to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Operator: "operator"
val kind = "operator"
assert_true(kind == "operator")
```

</details>

#### converts TypeParameter to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case TypeParameter: "type-parameter"
val kind = "type-parameter"
assert_true(kind == "type-parameter")
```

</details>

### SymbolKind description

#### describes File

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case File: "File symbol"
val desc = "File symbol"
assert_true(desc == "File symbol")
```

</details>

#### describes Module

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Module: "Module definition"
val desc = "Module definition"
assert_true(desc == "Module definition")
```

</details>

#### describes Namespace

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Namespace: "Namespace"
val desc = "Namespace"
assert_true(desc == "Namespace")
```

</details>

#### describes Package

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Package: "Package"
val desc = "Package"
assert_true(desc == "Package")
```

</details>

#### describes Class

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: "Class definition"
val desc = "Class definition"
assert_true(desc == "Class definition")
```

</details>

#### describes Method

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Method: "Method/member function"
val desc = "Method/member function"
assert_true(desc == "Method/member function")
```

</details>

#### describes Property

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Property: "Property"
val desc = "Property"
assert_true(desc == "Property")
```

</details>

#### describes Field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Field: "Field/member variable"
val desc = "Field/member variable"
assert_true(desc == "Field/member variable")
```

</details>

#### describes Constructor

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constructor: "Constructor"
val desc = "Constructor"
assert_true(desc == "Constructor")
```

</details>

#### describes Enum

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: "Enumeration type"
val desc = "Enumeration type"
assert_true(desc == "Enumeration type")
```

</details>

#### describes Interface

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: "Interface/trait"
val desc = "Interface/trait"
assert_true(desc == "Interface/trait")
```

</details>

#### describes Function

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Function: "Function"
val desc = "Function"
assert_true(desc == "Function")
```

</details>

#### describes Variable

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Variable: "Variable"
val desc = "Variable"
assert_true(desc == "Variable")
```

</details>

#### describes Constant

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constant: "Constant"
val desc = "Constant"
assert_true(desc == "Constant")
```

</details>

#### describes text

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case text: "text literal"
val desc = "text literal"
assert_true(desc == "text literal")
```

</details>

#### describes Number

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Number: "Number literal"
val desc = "Number literal"
assert_true(desc == "Number literal")
```

</details>

#### describes Boolean

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Boolean: "Boolean literal"
val desc = "Boolean literal"
assert_true(desc == "Boolean literal")
```

</details>

#### describes Array

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Array: "Array"
val desc = "Array"
assert_true(desc == "Array")
```

</details>

#### describes Object

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Object: "Object"
val desc = "Object"
assert_true(desc == "Object")
```

</details>

#### describes Key

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Key: "Object key"
val desc = "Object key"
assert_true(desc == "Object key")
```

</details>

#### describes Null

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Null: "Null value"
val desc = "Null value"
assert_true(desc == "Null value")
```

</details>

#### describes EnumMember

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case EnumMember: "Enum variant/member"
val desc = "Enum variant/member"
assert_true(desc == "Enum variant/member")
```

</details>

#### describes Struct

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: "Struct type"
val desc = "Struct type"
assert_true(desc == "Struct type")
```

</details>

#### describes Event

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Event: "Event"
val desc = "Event"
assert_true(desc == "Event")
```

</details>

#### describes Operator

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Operator: "Operator"
val desc = "Operator"
assert_true(desc == "Operator")
```

</details>

#### describes TypeParameter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case TypeParameter: "Type parameter/generic"
val desc = "Type parameter/generic"
assert_true(desc == "Type parameter/generic")
```

</details>

### SymbolKind is_type_definition

#### returns true for Class

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns true for Enum

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns true for Interface

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns true for Struct

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns false for other kinds

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_type = false
assert_false(is_type)
```

</details>

### SymbolKind is_callable

#### returns true for Method

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Method: true
val is_callable = true
assert_true(is_callable)
```

</details>

#### returns true for Function

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Function: true
val is_callable = true
assert_true(is_callable)
```

</details>

#### returns true for Constructor

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constructor: true
val is_callable = true
assert_true(is_callable)
```

</details>

#### returns false for other kinds

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_callable = false
assert_false(is_callable)
```

</details>

### SymbolKind is_container

#### returns true for File

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case File: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Module

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Module: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Namespace

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Namespace: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Package

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Package: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Class

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Enum

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Interface

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Struct

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns false for other kinds

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_container = false
assert_false(is_container)
```

</details>

### SymbolKind is_literal

#### returns true for text

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case text: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns true for Number

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Number: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns true for Boolean

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Boolean: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns true for Null

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Null: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns false for other kinds

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_literal = false
assert_false(is_literal)
```

</details>

### SymbolKind summary

#### categorizes as type

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_type_definition() (true)
val category = "type"
assert_true(category == "type")
```

</details>

#### categorizes as callable

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_callable() (true)
val category = "callable"
assert_true(category == "callable")
```

</details>

#### categorizes as container

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_container() (true)
val category = "container"
assert_true(category == "container")
```

</details>

#### categorizes as literal

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_literal() (true)
val category = "literal"
assert_true(category == "literal")
```

</details>

#### categorizes as value

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: else (default case)
val category = "value"
assert_true(category == "value")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/symbol_kind_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SymbolKind to_string
- SymbolKind description
- SymbolKind is_type_definition
- SymbolKind is_callable
- SymbolKind is_container
- SymbolKind is_literal
- SymbolKind summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
