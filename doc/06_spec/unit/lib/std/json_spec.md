# Json Specification

> Tests covering JsonValue, JsonPath, JsonBuilder, JsonArray, ToJson/FromJson, Convenience Functions, MsgPack, Integration, Use Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 73 | 73 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Specification

## Scenarios

### JsonValue

#### parse

#### should parse null

- should parse null


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse null")
val result = JsonValue__parse("null")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.is_null() to_be_true
```

</details>

#### should parse boolean true

- should parse boolean true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse boolean true")
val result = JsonValue__parse("true")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_bool().? to_be_true
expect json.as_bool().unwrap() to_be_true
```

</details>

#### should parse boolean false

- should parse boolean false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse boolean false")
val result = JsonValue__parse("false")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_bool().? to_be_true
expect json.as_bool().unwrap() to_be_false
```

</details>

#### should parse number

- should parse number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse number")
val result = JsonValue__parse("42")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_number().? to_be_true
expect json.as_number().unwrap() to_equal 42.0
```

</details>

#### should parse float number

- should parse float number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse float number")
val result = JsonValue__parse("3.14")
expect result.ok.? to_be_true

val json = result.unwrap()
val num = json.as_number().unwrap()
expect (num - 3.14).abs() < 0.001 to_be_true
```

</details>

#### should parse negative number

- should parse negative number


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse negative number")
val result = JsonValue__parse("-123")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_number().unwrap() to_equal -123.0
```

</details>

#### should parse string

- should parse string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse string")
val result = JsonValue__parse("\"hello\"")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_string().? to_be_true
expect json.as_string().unwrap() to_equal "hello"
```

</details>

#### should parse empty string

- should parse empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse empty string")
val result = JsonValue__parse("\"\"")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_string().unwrap() to_equal ""
```

</details>

#### should parse string with escapes

- should parse string with escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse string with escapes")
val result = JsonValue__parse("\"hello\\nworld\"")
expect result.ok.? to_be_true

val json = result.unwrap()
val str = json.as_string().unwrap()
expect str to_contain "hello"
expect str to_contain "world"
```

</details>

#### should parse empty array

- should parse empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse empty array")
val result = JsonValue__parse("[]")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_array().? to_be_true
expect json.as_array().unwrap().len() to_equal 0
```

</details>

#### should parse array with elements

- should parse array with elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse array with elements")
val result = JsonValue__parse("[1, 2, 3]")
expect result.ok.? to_be_true

val json = result.unwrap()
val arr = json.as_array().unwrap()
expect arr.len() to_equal 3
expect arr[0].as_number().unwrap() to_equal 1.0
expect arr[1].as_number().unwrap() to_equal 2.0
expect arr[2].as_number().unwrap() to_equal 3.0
```

</details>

#### should parse nested array

- should parse nested array


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse nested array")
val result = JsonValue__parse("[[1, 2], [3, 4]]")
expect result.ok.? to_be_true

val json = result.unwrap()
val arr = json.as_array().unwrap()
expect arr.len() to_equal 2
expect arr[0].as_array().unwrap().len() to_equal 2
expect arr[1].as_array().unwrap().len() to_equal 2
```

</details>

#### should parse empty object

- should parse empty object


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse empty object")
val result = JsonValue__parse(r"{}")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_object().? to_be_true
expect json.as_object().unwrap().len() to_equal 0
```

</details>

#### should parse object with fields

- should parse object with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse object with fields")
val result = JsonValue__parse("{\"name\": \"Alice\", \"age\": 30}")
expect result.ok.? to_be_true

val json = result.unwrap()
val obj = json.as_object().unwrap()
expect obj.len() to_equal 2
expect obj["name"].as_string().unwrap() to_equal "Alice"
expect obj["age"].as_number().unwrap() to_equal 30.0
```

</details>

#### should parse nested object

- should parse nested object


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse nested object")
val result = JsonValue__parse("{\"user\": {\"name\": \"Bob\"}}")
expect result.ok.? to_be_true

val json = result.unwrap()
val user = json.get("user").unwrap()
expect user.get("name").unwrap().as_string().unwrap() to_equal "Bob"
```

</details>

#### should fail on invalid JSON

- should fail on invalid JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should fail on invalid JSON")
val result = JsonValue__parse(r"{invalid")
expect result.err.? to_be_true
```

</details>

#### serialize

#### should serialize null

- should serialize null


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize null")
val json = JsonValue.Null
val text = json.serialize()
expect text to_equal "null"
```

</details>

#### should serialize boolean

- should serialize boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize boolean")
val json = JsonValue.Bool(true)
expect json.serialize() to_equal "true"
```

</details>

#### should serialize number

- should serialize number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize number")
val json = JsonValue.Number(42.0)
val text = json.serialize()
expect text to_contain "42"
```

</details>

#### should serialize string

- should serialize string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize string")
val json = JsonValue.String("hello")
expect json.serialize() to_equal "\"hello\""
```

</details>

#### should serialize empty array

- should serialize empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize empty array")
val json = JsonValue.Array([])
expect json.serialize() to_equal "[]"
```

</details>

#### should serialize array

- should serialize array


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize array")
val json = JsonValue.Array([
    JsonValue.Number(1.0),
    JsonValue.Number(2.0),
    JsonValue.Number(3.0)
])
val text = json.serialize()
expect text to_contain "1"
expect text to_contain "2"
expect text to_contain "3"
```

</details>

#### should serialize empty object

- should serialize empty object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize empty object")
val json = JsonValue.Object({})
expect json.serialize() to_equal "{}"
```

</details>

#### should serialize object

- should serialize object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize object")
val json = JsonValue.Object({
    "name": JsonValue.String("Alice"),
    "age": JsonValue.Number(30.0)
})
val text = json.serialize()
expect text to_contain "name"
expect text to_contain "Alice"
expect text to_contain "age"
```

</details>

#### pretty

#### should pretty print object

- should pretty print object


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should pretty print object")
val json = JsonValue.Object({
    "name": JsonValue.String("Alice"),
    "age": JsonValue.Number(30.0)
})
val text = json.pretty()
expect text to_contain "name"
expect text to_contain "Alice"
# Pretty output should have indentation
expect text.len() > json.serialize().len() to_be_true
```

</details>

#### get

#### should get object field

- should get object field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should get object field")
val json = JsonValue.Object({
    "name": JsonValue.String("Alice")
})
val name = json.get("name")
expect name.? to_be_true
expect name.unwrap().as_string().unwrap() to_equal "Alice"
```

</details>

#### should return None for missing field

- should return None for missing field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return None for missing field")
val json = JsonValue.Object({})
val missing = json.get("missing")
expect missing.? to_be_false
```

</details>

#### should return None for non-object

- should return None for non-object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return None for non-object")
val json = JsonValue.String("not an object")
val result = json.get("field")
expect result.? to_be_false
```

</details>

#### get_index

#### should get array element

- should get array element


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should get array element")
val json = JsonValue.Array([
    JsonValue.String("first"),
    JsonValue.String("second")
])
val first = json.get_index(0)
expect first.? to_be_true
expect first.unwrap().as_string().unwrap() to_equal "first"
```

</details>

#### should return None for out of bounds

- should return None for out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return None for out of bounds")
val json = JsonValue.Array([])
val result = json.get_index(0)
expect result.? to_be_false
```

</details>

#### should return None for non-array

- should return None for non-array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return None for non-array")
val json = JsonValue.String("not an array")
val result = json.get_index(0)
expect result.? to_be_false
```

</details>

#### type_name

#### should return correct type names

- should return correct type names


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return correct type names")
expect JsonValue.Null__type_name() to_equal "null"
expect JsonValue.Bool(true).type_name() to_equal "boolean"
expect JsonValue.Number(42.0).type_name() to_equal "number"
expect JsonValue.String("text").type_name() to_equal "string"
expect JsonValue.Array([]).type_name() to_equal "array"
expect JsonValue.Object({}).type_name() to_equal "object"
```

</details>

### JsonPath

#### query

#### should query simple field

- should query simple field


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should query simple field")
val json = JsonValue.Object({
    "name": JsonValue.String("Alice")
})
val path = JsonPath__new("name")
val result = path.query(json)
expect result.? to_be_true
expect result.unwrap().as_string().unwrap() to_equal "Alice"
```

</details>

#### should query nested field

- should query nested field


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should query nested field")
val json = JsonValue.Object({
    "user": JsonValue.Object({
        "name": JsonValue.String("Bob")
    })
})
val path = JsonPath__new("user.name")
val result = path.query(json)
expect result.? to_be_true
expect result.unwrap().as_string().unwrap() to_equal "Bob"
```

</details>

#### should query array index

- should query array index


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should query array index")
val json = JsonValue.Array([
    JsonValue.String("first"),
    JsonValue.String("second")
])
val path = JsonPath__new("0")
val result = path.query(json)
expect result.? to_be_true
expect result.unwrap().as_string().unwrap() to_equal "first"
```

</details>

#### should query mixed path

- should query mixed path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should query mixed path")
val json = JsonValue.Object({
    "users": JsonValue.Array([
        JsonValue.Object({
            "name": JsonValue.String("Alice")
        })
    ])
})
val path = JsonPath__new("users.0.name")
val result = path.query(json)
expect result.? to_be_true
expect result.unwrap().as_string().unwrap() to_equal "Alice"
```

</details>

#### should return None for invalid path

- should return None for invalid path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return None for invalid path")
val json = JsonValue.Object({})
val path = JsonPath__new("missing.field")
val result = path.query(json)
expect result.? to_be_false
```

</details>

### JsonBuilder

#### construction

#### should build empty object

- should build empty object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should build empty object")
val builder = JsonBuilder__new()
val json = builder.build()
expect json.as_object().unwrap().len() to_equal 0
```

</details>

#### should build object with fields

- should build object with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should build object with fields")
val json = JsonBuilder__new()
    .put("name", JsonValue.String("Alice"))
    .put("age", JsonValue.Number(30.0))
    .build()

val obj = json.as_object().unwrap()
expect obj.len() to_equal 2
expect obj["name"].as_string().unwrap() to_equal "Alice"
expect obj["age"].as_number().unwrap() to_equal 30.0
```

</details>

#### convenience methods

#### should put string

- should put string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should put string")
val json = JsonBuilder__new()
    .put_string("name", "Alice")
    .build()

val name = json.get("name").unwrap().as_string().unwrap()
expect name to_equal "Alice"
```

</details>

#### should put number

- should put number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should put number")
val json = JsonBuilder__new()
    .put_number("age", 30.0)
    .build()

val age = json.get("age").unwrap().as_number().unwrap()
expect age to_equal 30.0
```

</details>

#### should put boolean

- should put boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should put boolean")
val json = JsonBuilder__new()
    .put_bool("active", true)
    .build()

val active = json.get("active").unwrap().as_bool().unwrap()
expect active to_be_true
```

</details>

#### should put null

- should put null


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should put null")
val json = JsonBuilder__new()
    .put_null("value")
    .build()

val value = json.get("value").unwrap()
expect value.is_null() to_be_true
```

</details>

### JsonArray

#### construction

#### should build empty array

- should build empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should build empty array")
val builder = JsonArray__new()
val json = builder.build()
expect json.as_array().unwrap().len() to_equal 0
```

</details>

#### should build array with elements

- should build array with elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should build array with elements")
val json = JsonArray__new()
    .push(JsonValue.Number(1.0))
    .push(JsonValue.Number(2.0))
    .push(JsonValue.Number(3.0))
    .build()

val arr = json.as_array().unwrap()
expect arr.len() to_equal 3
expect arr[0].as_number().unwrap() to_equal 1.0
expect arr[2].as_number().unwrap() to_equal 3.0
```

</details>

#### convenience methods

#### should push string

- should push string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should push string")
val json = JsonArray__new()
    .push_string("hello")
    .build()

val arr = json.as_array().unwrap()
expect arr[0].as_string().unwrap() to_equal "hello"
```

</details>

#### should push number

- should push number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should push number")
val json = JsonArray__new()
    .push_number(42.0)
    .build()

val arr = json.as_array().unwrap()
expect arr[0].as_number().unwrap() to_equal 42.0
```

</details>

#### should push boolean

- should push boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should push boolean")
val json = JsonArray__new()
    .push_bool(true)
    .build()

val arr = json.as_array().unwrap()
expect arr[0].as_bool().unwrap() to_be_true
```

</details>

#### should push null

- should push null


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should push null")
val json = JsonArray__new()
    .push_null()
    .build()

val arr = json.as_array().unwrap()
expect arr[0].is_null() to_be_true
```

</details>

### ToJson/FromJson

#### custom type serialization

#### should serialize custom type

- should serialize custom type


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize custom type")
# This test demonstrates the trait pattern
# In real code, you'd implement ToJson for your types
val json = JsonBuilder__new()
    .put_string("name", "Alice")
    .put_number("age", 30.0)
    .build()

expect json.as_object().? to_be_true
```

</details>

#### should deserialize custom type

- should deserialize custom type


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should deserialize custom type")
# This test demonstrates the trait pattern
val json = JsonValue__parse("{\"name\": \"Bob\", \"age\": 25}").unwrap()
val name = json.get("name").unwrap().as_string().unwrap()
val age = json.get("age").unwrap().as_number().unwrap()

expect name to_equal "Bob"
expect age to_equal 25.0
```

</details>

### Convenience Functions

#### parse_json

#### should parse JSON text

- should parse JSON text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse JSON text")
val result = parse_json("{\"key\": \"value\"}")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.get("key").unwrap().as_string().unwrap() to_equal "value"
```

</details>

#### to_json_string

#### should serialize to string

- should serialize to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize to string")
val json = JsonValue.Object({
    "key": JsonValue.String("value")
})
val text = to_json_string(json)
expect text to_contain "key"
expect text to_contain "value"
```

</details>

#### to_json_pretty

#### should serialize to pretty string

- should serialize to pretty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should serialize to pretty string")
val json = JsonValue.Object({
    "key": JsonValue.String("value")
})
val text = to_json_pretty(json)
expect text to_contain "key"
expect text to_contain "value"
```

</details>

#### object

#### should create object from pairs

- should create object from pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create object from pairs")
val json = object([
    ("name", JsonValue.String("Alice")),
    ("age", JsonValue.Number(30.0))
])

val obj = json.as_object().unwrap()
expect obj["name"].as_string().unwrap() to_equal "Alice"
expect obj["age"].as_number().unwrap() to_equal 30.0
```

</details>

#### array

#### should create array from values

- should create array from values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create array from values")
val json = array([
    JsonValue.Number(1.0),
    JsonValue.Number(2.0),
    JsonValue.Number(3.0)
])

val arr = json.as_array().unwrap()
expect arr.len() to_equal 3
expect arr[1].as_number().unwrap() to_equal 2.0
```

</details>

### MsgPack

#### encode

#### should encode null

- should encode null


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should encode null")
val json = JsonValue.Null
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode boolean

- should encode boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should encode boolean")
val json = JsonValue.Bool(true)
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode number

- should encode number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should encode number")
val json = JsonValue.Number(42.0)
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode string

- should encode string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should encode string")
val json = JsonValue.String("hello")
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode array

- should encode array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should encode array")
val json = JsonValue.Array([
    JsonValue.Number(1.0),
    JsonValue.Number(2.0)
])
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode object

- should encode object


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should encode object")
val json = JsonValue.Object({
    "key": JsonValue.String("value")
})
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### decode

#### should decode encoded data

- should decode encoded data


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should decode encoded data")
val original = JsonValue.Number(42.0)
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes)

expect decoded.? to_be_true
expect decoded.unwrap().as_number().unwrap() to_equal 42.0
```

</details>

#### round-trip

#### should round-trip null

- should round-trip null


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round-trip null")
val original = JsonValue.Null
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
expect decoded.is_null() to_be_true
```

</details>

#### should round-trip boolean

- should round-trip boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round-trip boolean")
val original = JsonValue.Bool(true)
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
expect decoded.as_bool().unwrap() to_be_true
```

</details>

#### should round-trip string

- should round-trip string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round-trip string")
val original = JsonValue.String("hello world")
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
expect decoded.as_string().unwrap() to_equal "hello world"
```

</details>

#### should round-trip array

- should round-trip array


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round-trip array")
val original = JsonValue.Array([
    JsonValue.Number(1.0),
    JsonValue.Number(2.0),
    JsonValue.Number(3.0)
])
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
val arr = decoded.as_array().unwrap()
expect arr.len() to_equal 3
```

</details>

#### should round-trip object

- should round-trip object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round-trip object")
val original = JsonValue.Object({
    "name": JsonValue.String("Alice"),
    "age": JsonValue.Number(30.0)
})
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
val obj = decoded.as_object().unwrap()
expect obj["name"].as_string().unwrap() to_equal "Alice"
```

</details>

### Integration

#### JSON round-trip

#### should round-trip complex object

- should round-trip complex object


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should round-trip complex object")
val original = JsonValue.Object({
    "user": JsonValue.Object({
        "name": JsonValue.String("Alice"),
        "age": JsonValue.Number(30.0),
        "active": JsonValue.Bool(true)
    }),
    "tags": JsonValue.Array([
        JsonValue.String("admin"),
        JsonValue.String("user")
    ])
})

val text = original.serialize()
val parsed = JsonValue__parse(text).unwrap()

val user = parsed.get("user").unwrap()
expect user.get("name").unwrap().as_string().unwrap() to_equal "Alice"
expect user.get("age").unwrap().as_number().unwrap() to_equal 30.0
expect user.get("active").unwrap().as_bool().unwrap() to_be_true

val tags = parsed.get("tags").unwrap().as_array().unwrap()
expect tags.len() to_equal 2
```

</details>

#### Path query on complex data

#### should query deeply nested data

- should query deeply nested data


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should query deeply nested data")
val json = JsonValue.Object({
    "data": JsonValue.Object({
        "users": JsonValue.Array([
            JsonValue.Object({
                "profile": JsonValue.Object({
                    "name": JsonValue.String("Alice")
                })
            })
        ])
    })
})

val path = JsonPath__new("data.users.0.profile.name")
val result = path.query(json)
expect result.? to_be_true
expect result.unwrap().as_string().unwrap() to_equal "Alice"
```

</details>

### Use Cases

#### API response parsing

#### should parse API response

- should parse API response


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should parse API response")
val response = "{\"status\": \"ok\", \"data\": {\"id\": 123}}"
val json = JsonValue__parse(response).unwrap()

val status = json.get("status").unwrap().as_string().unwrap()
expect status to_equal "ok"

val data = json.get("data").unwrap()
val id = data.get("id").unwrap().as_number().unwrap()
expect id to_equal 123.0
```

</details>

#### Config file

#### should build config object

- should build config object


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should build config object")
val config = JsonBuilder__new()
    .put_string("host", "localhost")
    .put_number("port", 8080.0)
    .put_bool("debug", true)
    .build()

val text = config.pretty()
expect text to_contain "host"
expect text to_contain "localhost"
expect text to_contain "port"
```

</details>

#### Data transformation

#### should transform data structure

- should transform data structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should transform data structure")
val input = JsonValue__parse("[1, 2, 3]").unwrap()
val arr = input.as_array().unwrap()

var builder = JsonArray__new()
for item in arr:
    val num = item.as_number().unwrap()
    builder = builder.push_number(num * 2.0)

val output = builder.build()
val result = output.as_array().unwrap()
expect result[0].as_number().unwrap() to_equal 2.0
expect result[1].as_number().unwrap() to_equal 4.0
expect result[2].as_number().unwrap() to_equal 6.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JsonValue, JsonPath, JsonBuilder, JsonArray, ToJson/FromJson, Convenience Functions, MsgPack, Integration, Use Cases.
- JsonValue
- JsonPath
- JsonBuilder
- JsonArray
- ToJson/FromJson
- Convenience Functions
- MsgPack
- Integration
- Use Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 73 |
| Active scenarios | 73 |
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

- Canonical SPipe generation for source `0a817c92ade3641d6299bd53e582e59100cfa519901558cdc6f600107555d84b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a817c92ade3641d6299bd53e582e59100cfa519901558cdc6f600107555d84b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a817c92ade3641d6299bd53e582e59100cfa519901558cdc6f600107555d84b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/std/json_spec.spl
mirror: doc/06_spec/unit/lib/std/json_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/json_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse null' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/json_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse null' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/json_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse boolean true' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/json_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse boolean true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/json_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse boolean false' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/json_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse boolean false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/json_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse number' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/json_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse float number' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/json_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse negative number' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
