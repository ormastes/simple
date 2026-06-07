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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case File: "file"
val kind = "file"
expect(kind == "file")
```

</details>

#### converts Module to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Module: "module"
val kind = "module"
expect(kind == "module")
```

</details>

#### converts Namespace to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Namespace: "namespace"
val kind = "namespace"
expect(kind == "namespace")
```

</details>

#### converts Package to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Package: "package"
val kind = "package"
expect(kind == "package")
```

</details>

#### converts Class to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: "class"
val kind = "class"
expect(kind == "class")
```

</details>

#### converts Method to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Method: "method"
val kind = "method"
expect(kind == "method")
```

</details>

#### converts Property to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Property: "property"
val kind = "property"
expect(kind == "property")
```

</details>

#### converts Field to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Field: "field"
val kind = "field"
expect(kind == "field")
```

</details>

#### converts Constructor to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constructor: "constructor"
val kind = "constructor"
expect(kind == "constructor")
```

</details>

#### converts Enum to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: "enum"
val kind = "enum"
expect(kind == "enum")
```

</details>

#### converts Interface to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: "interface"
val kind = "interface"
expect(kind == "interface")
```

</details>

#### converts Function to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Function: "function"
val kind = "function"
expect(kind == "function")
```

</details>

#### converts Variable to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Variable: "variable"
val kind = "variable"
expect(kind == "variable")
```

</details>

#### converts Constant to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constant: "constant"
val kind = "constant"
expect(kind == "constant")
```

</details>

#### converts text to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case text: "string"
val kind = "string"
expect(kind == "string")
```

</details>

#### converts Number to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Number: "number"
val kind = "number"
expect(kind == "number")
```

</details>

#### converts Boolean to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Boolean: "boolean"
val kind = "boolean"
expect(kind == "boolean")
```

</details>

#### converts Array to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Array: "array"
val kind = "array"
expect(kind == "array")
```

</details>

#### converts Object to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Object: "object"
val kind = "object"
expect(kind == "object")
```

</details>

#### converts Key to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Key: "key"
val kind = "key"
expect(kind == "key")
```

</details>

#### converts Null to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Null: "null"
val kind = "null"
expect(kind == "null")
```

</details>

#### converts EnumMember to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case EnumMember: "enum-member"
val kind = "enum-member"
expect(kind == "enum-member")
```

</details>

#### converts Struct to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: "struct"
val kind = "struct"
expect(kind == "struct")
```

</details>

#### converts Event to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Event: "event"
val kind = "event"
expect(kind == "event")
```

</details>

#### converts Operator to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Operator: "operator"
val kind = "operator"
expect(kind == "operator")
```

</details>

#### converts TypeParameter to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case TypeParameter: "type-parameter"
val kind = "type-parameter"
expect(kind == "type-parameter")
```

</details>

### SymbolKind description

#### describes File

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case File: "File symbol"
val desc = "File symbol"
expect(desc == "File symbol")
```

</details>

#### describes Module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Module: "Module definition"
val desc = "Module definition"
expect(desc == "Module definition")
```

</details>

#### describes Namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Namespace: "Namespace"
val desc = "Namespace"
expect(desc == "Namespace")
```

</details>

#### describes Package

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Package: "Package"
val desc = "Package"
expect(desc == "Package")
```

</details>

#### describes Class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: "Class definition"
val desc = "Class definition"
expect(desc == "Class definition")
```

</details>

#### describes Method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Method: "Method/member function"
val desc = "Method/member function"
expect(desc == "Method/member function")
```

</details>

#### describes Property

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Property: "Property"
val desc = "Property"
expect(desc == "Property")
```

</details>

#### describes Field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Field: "Field/member variable"
val desc = "Field/member variable"
expect(desc == "Field/member variable")
```

</details>

#### describes Constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constructor: "Constructor"
val desc = "Constructor"
expect(desc == "Constructor")
```

</details>

#### describes Enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: "Enumeration type"
val desc = "Enumeration type"
expect(desc == "Enumeration type")
```

</details>

#### describes Interface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: "Interface/trait"
val desc = "Interface/trait"
expect(desc == "Interface/trait")
```

</details>

#### describes Function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Function: "Function"
val desc = "Function"
expect(desc == "Function")
```

</details>

#### describes Variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Variable: "Variable"
val desc = "Variable"
expect(desc == "Variable")
```

</details>

#### describes Constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constant: "Constant"
val desc = "Constant"
expect(desc == "Constant")
```

</details>

#### describes text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case text: "text literal"
val desc = "text literal"
expect(desc == "text literal")
```

</details>

#### describes Number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Number: "Number literal"
val desc = "Number literal"
expect(desc == "Number literal")
```

</details>

#### describes Boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Boolean: "Boolean literal"
val desc = "Boolean literal"
expect(desc == "Boolean literal")
```

</details>

#### describes Array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Array: "Array"
val desc = "Array"
expect(desc == "Array")
```

</details>

#### describes Object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Object: "Object"
val desc = "Object"
expect(desc == "Object")
```

</details>

#### describes Key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Key: "Object key"
val desc = "Object key"
expect(desc == "Object key")
```

</details>

#### describes Null

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Null: "Null value"
val desc = "Null value"
expect(desc == "Null value")
```

</details>

#### describes EnumMember

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case EnumMember: "Enum variant/member"
val desc = "Enum variant/member"
expect(desc == "Enum variant/member")
```

</details>

#### describes Struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: "Struct type"
val desc = "Struct type"
expect(desc == "Struct type")
```

</details>

#### describes Event

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Event: "Event"
val desc = "Event"
expect(desc == "Event")
```

</details>

#### describes Operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Operator: "Operator"
val desc = "Operator"
expect(desc == "Operator")
```

</details>

#### describes TypeParameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case TypeParameter: "Type parameter/generic"
val desc = "Type parameter/generic"
expect(desc == "Type parameter/generic")
```

</details>

### SymbolKind is_type_definition

#### returns true for Class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: true
val is_type = true
expect(is_type)
```

</details>

#### returns true for Enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: true
val is_type = true
expect(is_type)
```

</details>

#### returns true for Interface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: true
val is_type = true
expect(is_type)
```

</details>

#### returns true for Struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: true
val is_type = true
expect(is_type)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_type = false
expect(not is_type)
```

</details>

### SymbolKind is_callable

#### returns true for Method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Method: true
val is_callable = true
expect(is_callable)
```

</details>

#### returns true for Function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Function: true
val is_callable = true
expect(is_callable)
```

</details>

#### returns true for Constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Constructor: true
val is_callable = true
expect(is_callable)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_callable = false
expect(not is_callable)
```

</details>

### SymbolKind is_container

#### returns true for File

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case File: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Module: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Namespace: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Package

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Package: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Class: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Enum: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Interface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Interface: true
val is_container = true
expect(is_container)
```

</details>

#### returns true for Struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Struct: true
val is_container = true
expect(is_container)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_container = false
expect(not is_container)
```

</details>

### SymbolKind is_literal

#### returns true for text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case text: true
val is_literal = true
expect(is_literal)
```

</details>

#### returns true for Number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Number: true
val is_literal = true
expect(is_literal)
```

</details>

#### returns true for Boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Boolean: true
val is_literal = true
expect(is_literal)
```

</details>

#### returns true for Null

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Null: true
val is_literal = true
expect(is_literal)
```

</details>

#### returns false for other kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_literal = false
expect(not is_literal)
```

</details>

### SymbolKind summary

#### categorizes as type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_type_definition() (true)
val category = "type"
expect(category == "type")
```

</details>

#### categorizes as callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_callable() (true)
val category = "callable"
expect(category == "callable")
```

</details>

#### categorizes as container

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_container() (true)
val category = "container"
expect(category == "container")
```

</details>

#### categorizes as literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: elif self.is_literal() (true)
val category = "literal"
expect(category == "literal")
```

</details>

#### categorizes as value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: else (default case)
val category = "value"
expect(category == "value")
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
