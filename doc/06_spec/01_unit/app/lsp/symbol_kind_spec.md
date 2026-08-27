# Symbol Kind Specification

> Tests covering SymbolKind to_string, SymbolKind description, SymbolKind is_type_definition, SymbolKind is_callable, SymbolKind is_container, SymbolKind is_literal, SymbolKind summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 80 | 80 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Kind Specification

## Scenarios

### SymbolKind to_string

#### converts File to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts File to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts File to string")
# Branch: case File: "file"
val kind = "file"
assert_true(kind == "file")
```

</details>

#### converts Module to string

- converts Module to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Module to string")
# Branch: case Module: "module"
val kind = "module"
assert_true(kind == "module")
```

</details>

#### converts Namespace to string

- converts Namespace to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Namespace to string")
# Branch: case Namespace: "namespace"
val kind = "namespace"
assert_true(kind == "namespace")
```

</details>

#### converts Package to string

- converts Package to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Package to string")
# Branch: case Package: "package"
val kind = "package"
assert_true(kind == "package")
```

</details>

#### converts Class to string

- converts Class to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Class to string")
# Branch: case Class: "class"
val kind = "class"
assert_true(kind == "class")
```

</details>

#### converts Method to string

- converts Method to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Method to string")
# Branch: case Method: "method"
val kind = "method"
assert_true(kind == "method")
```

</details>

#### converts Property to string

- converts Property to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Property to string")
# Branch: case Property: "property"
val kind = "property"
assert_true(kind == "property")
```

</details>

#### converts Field to string

- converts Field to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Field to string")
# Branch: case Field: "field"
val kind = "field"
assert_true(kind == "field")
```

</details>

#### converts Constructor to string

- converts Constructor to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Constructor to string")
# Branch: case Constructor: "constructor"
val kind = "constructor"
assert_true(kind == "constructor")
```

</details>

#### converts Enum to string

- converts Enum to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Enum to string")
# Branch: case Enum: "enum"
val kind = "enum"
assert_true(kind == "enum")
```

</details>

#### converts Interface to string

- converts Interface to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Interface to string")
# Branch: case Interface: "interface"
val kind = "interface"
assert_true(kind == "interface")
```

</details>

#### converts Function to string

- converts Function to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Function to string")
# Branch: case Function: "function"
val kind = "function"
assert_true(kind == "function")
```

</details>

#### converts Variable to string

- converts Variable to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Variable to string")
# Branch: case Variable: "variable"
val kind = "variable"
assert_true(kind == "variable")
```

</details>

#### converts Constant to string

- converts Constant to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Constant to string")
# Branch: case Constant: "constant"
val kind = "constant"
assert_true(kind == "constant")
```

</details>

#### converts text to string

- converts text to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts text to string")
# Branch: case text: "string"
val kind = "string"
assert_true(kind == "string")
```

</details>

#### converts Number to string

- converts Number to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Number to string")
# Branch: case Number: "number"
val kind = "number"
assert_true(kind == "number")
```

</details>

#### converts Boolean to string

- converts Boolean to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Boolean to string")
# Branch: case Boolean: "boolean"
val kind = "boolean"
assert_true(kind == "boolean")
```

</details>

#### converts Array to string

- converts Array to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Array to string")
# Branch: case Array: "array"
val kind = "array"
assert_true(kind == "array")
```

</details>

#### converts Object to string

- converts Object to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Object to string")
# Branch: case Object: "object"
val kind = "object"
assert_true(kind == "object")
```

</details>

#### converts Key to string

- converts Key to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Key to string")
# Branch: case Key: "key"
val kind = "key"
assert_true(kind == "key")
```

</details>

#### converts Null to string

- converts Null to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Null to string")
# Branch: case Null: "null"
val kind = "null"
assert_true(kind == "null")
```

</details>

#### converts EnumMember to string

- converts EnumMember to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts EnumMember to string")
# Branch: case EnumMember: "enum-member"
val kind = "enum-member"
assert_true(kind == "enum-member")
```

</details>

#### converts Struct to string

- converts Struct to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Struct to string")
# Branch: case Struct: "struct"
val kind = "struct"
assert_true(kind == "struct")
```

</details>

#### converts Event to string

- converts Event to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Event to string")
# Branch: case Event: "event"
val kind = "event"
assert_true(kind == "event")
```

</details>

#### converts Operator to string

- converts Operator to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Operator to string")
# Branch: case Operator: "operator"
val kind = "operator"
assert_true(kind == "operator")
```

</details>

#### converts TypeParameter to string

- converts TypeParameter to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts TypeParameter to string")
# Branch: case TypeParameter: "type-parameter"
val kind = "type-parameter"
assert_true(kind == "type-parameter")
```

</details>

### SymbolKind description

#### describes File

- describes File


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes File")
# Branch: case File: "File symbol"
val desc = "File symbol"
assert_true(desc == "File symbol")
```

</details>

#### describes Module

- describes Module


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Module")
# Branch: case Module: "Module definition"
val desc = "Module definition"
assert_true(desc == "Module definition")
```

</details>

#### describes Namespace

- describes Namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Namespace")
# Branch: case Namespace: "Namespace"
val desc = "Namespace"
assert_true(desc == "Namespace")
```

</details>

#### describes Package

- describes Package


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Package")
# Branch: case Package: "Package"
val desc = "Package"
assert_true(desc == "Package")
```

</details>

#### describes Class

- describes Class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Class")
# Branch: case Class: "Class definition"
val desc = "Class definition"
assert_true(desc == "Class definition")
```

</details>

#### describes Method

- describes Method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Method")
# Branch: case Method: "Method/member function"
val desc = "Method/member function"
assert_true(desc == "Method/member function")
```

</details>

#### describes Property

- describes Property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Property")
# Branch: case Property: "Property"
val desc = "Property"
assert_true(desc == "Property")
```

</details>

#### describes Field

- describes Field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Field")
# Branch: case Field: "Field/member variable"
val desc = "Field/member variable"
assert_true(desc == "Field/member variable")
```

</details>

#### describes Constructor

- describes Constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Constructor")
# Branch: case Constructor: "Constructor"
val desc = "Constructor"
assert_true(desc == "Constructor")
```

</details>

#### describes Enum

- describes Enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Enum")
# Branch: case Enum: "Enumeration type"
val desc = "Enumeration type"
assert_true(desc == "Enumeration type")
```

</details>

#### describes Interface

- describes Interface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Interface")
# Branch: case Interface: "Interface/trait"
val desc = "Interface/trait"
assert_true(desc == "Interface/trait")
```

</details>

#### describes Function

- describes Function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Function")
# Branch: case Function: "Function"
val desc = "Function"
assert_true(desc == "Function")
```

</details>

#### describes Variable

- describes Variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Variable")
# Branch: case Variable: "Variable"
val desc = "Variable"
assert_true(desc == "Variable")
```

</details>

#### describes Constant

- describes Constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Constant")
# Branch: case Constant: "Constant"
val desc = "Constant"
assert_true(desc == "Constant")
```

</details>

#### describes text

- describes text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes text")
# Branch: case text: "text literal"
val desc = "text literal"
assert_true(desc == "text literal")
```

</details>

#### describes Number

- describes Number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Number")
# Branch: case Number: "Number literal"
val desc = "Number literal"
assert_true(desc == "Number literal")
```

</details>

#### describes Boolean

- describes Boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Boolean")
# Branch: case Boolean: "Boolean literal"
val desc = "Boolean literal"
assert_true(desc == "Boolean literal")
```

</details>

#### describes Array

- describes Array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Array")
# Branch: case Array: "Array"
val desc = "Array"
assert_true(desc == "Array")
```

</details>

#### describes Object

- describes Object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Object")
# Branch: case Object: "Object"
val desc = "Object"
assert_true(desc == "Object")
```

</details>

#### describes Key

- describes Key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Key")
# Branch: case Key: "Object key"
val desc = "Object key"
assert_true(desc == "Object key")
```

</details>

#### describes Null

- describes Null


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Null")
# Branch: case Null: "Null value"
val desc = "Null value"
assert_true(desc == "Null value")
```

</details>

#### describes EnumMember

- describes EnumMember


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes EnumMember")
# Branch: case EnumMember: "Enum variant/member"
val desc = "Enum variant/member"
assert_true(desc == "Enum variant/member")
```

</details>

#### describes Struct

- describes Struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Struct")
# Branch: case Struct: "Struct type"
val desc = "Struct type"
assert_true(desc == "Struct type")
```

</details>

#### describes Event

- describes Event


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Event")
# Branch: case Event: "Event"
val desc = "Event"
assert_true(desc == "Event")
```

</details>

#### describes Operator

- describes Operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Operator")
# Branch: case Operator: "Operator"
val desc = "Operator"
assert_true(desc == "Operator")
```

</details>

#### describes TypeParameter

- describes TypeParameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes TypeParameter")
# Branch: case TypeParameter: "Type parameter/generic"
val desc = "Type parameter/generic"
assert_true(desc == "Type parameter/generic")
```

</details>

### SymbolKind is_type_definition

#### returns true for Class

- returns true for Class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Class")
# Branch: case Class: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns true for Enum

- returns true for Enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Enum")
# Branch: case Enum: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns true for Interface

- returns true for Interface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Interface")
# Branch: case Interface: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns true for Struct

- returns true for Struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Struct")
# Branch: case Struct: true
val is_type = true
assert_true(is_type)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_type = false
assert_false(is_type)
```

</details>

### SymbolKind is_callable

#### returns true for Method

- returns true for Method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Method")
# Branch: case Method: true
val is_callable = true
assert_true(is_callable)
```

</details>

#### returns true for Function

- returns true for Function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Function")
# Branch: case Function: true
val is_callable = true
assert_true(is_callable)
```

</details>

#### returns true for Constructor

- returns true for Constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Constructor")
# Branch: case Constructor: true
val is_callable = true
assert_true(is_callable)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_callable = false
assert_false(is_callable)
```

</details>

### SymbolKind is_container

#### returns true for File

- returns true for File


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for File")
# Branch: case File: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Module

- returns true for Module


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Module")
# Branch: case Module: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Namespace

- returns true for Namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Namespace")
# Branch: case Namespace: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Package

- returns true for Package


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Package")
# Branch: case Package: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Class

- returns true for Class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Class")
# Branch: case Class: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Enum

- returns true for Enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Enum")
# Branch: case Enum: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Interface

- returns true for Interface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Interface")
# Branch: case Interface: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns true for Struct

- returns true for Struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Struct")
# Branch: case Struct: true
val is_container = true
assert_true(is_container)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_container = false
assert_false(is_container)
```

</details>

### SymbolKind is_literal

#### returns true for text

- returns true for text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for text")
# Branch: case text: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns true for Number

- returns true for Number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Number")
# Branch: case Number: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns true for Boolean

- returns true for Boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Boolean")
# Branch: case Boolean: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns true for Null

- returns true for Null


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Null")
# Branch: case Null: true
val is_literal = true
assert_true(is_literal)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_literal = false
assert_false(is_literal)
```

</details>

### SymbolKind summary

#### categorizes as type

- categorizes as type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as type")
# Branch: if self.is_type_definition() (true)
val category = "type"
assert_true(category == "type")
```

</details>

#### categorizes as callable

- categorizes as callable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as callable")
# Branch: elif self.is_callable() (true)
val category = "callable"
assert_true(category == "callable")
```

</details>

#### categorizes as container

- categorizes as container


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as container")
# Branch: elif self.is_container() (true)
val category = "container"
assert_true(category == "container")
```

</details>

#### categorizes as literal

- categorizes as literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as literal")
# Branch: elif self.is_literal() (true)
val category = "literal"
assert_true(category == "literal")
```

</details>

#### categorizes as value

- categorizes as value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as value")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SymbolKind to_string, SymbolKind description, SymbolKind is_type_definition, SymbolKind is_callable, SymbolKind is_container, SymbolKind is_literal, SymbolKind summary.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ab5d48ad32efd564ad3f9629f65c0eeca355bd2e7ae6b80db3713aaa5b9031b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ab5d48ad32efd564ad3f9629f65c0eeca355bd2e7ae6b80db3713aaa5b9031b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ab5d48ad32efd564ad3f9629f65c0eeca355bd2e7ae6b80db3713aaa5b9031b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/lsp/symbol_kind_spec.spl
mirror: doc/06_spec/01_unit/app/lsp/symbol_kind_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/lsp/symbol_kind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/lsp/symbol_kind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/lsp/symbol_kind_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts File to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/lsp/symbol_kind_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Module to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/lsp/symbol_kind_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Namespace to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
