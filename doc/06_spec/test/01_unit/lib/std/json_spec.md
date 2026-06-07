# Json Specification

> 1. expect json is null

<!-- sdn-diagram:id=json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect json is null


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("null")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.is_null() to_be_true
```

</details>

#### should parse boolean true

1. expect json as bool
2. expect json as bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("true")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_bool().? to_be_true
expect json.as_bool().unwrap() to_be_true
```

</details>

#### should parse boolean false

1. expect json as bool
2. expect json as bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("false")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_bool().? to_be_true
expect json.as_bool().unwrap() to_be_false
```

</details>

#### should parse number

1. expect json as number
2. expect json as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("42")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_number().? to_be_true
expect json.as_number().unwrap() to_equal 42.0
```

</details>

#### should parse float number

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("3.14")
expect result.ok.? to_be_true

val json = result.unwrap()
val num = json.as_number().unwrap()
expect (num - 3.14).abs() < 0.001 to_be_true
```

</details>

#### should parse negative number

1. expect json as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("-123")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_number().unwrap() to_equal -123.0
```

</details>

#### should parse string

1. expect json as string
2. expect json as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("\"hello\"")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_string().? to_be_true
expect json.as_string().unwrap() to_equal "hello"
```

</details>

#### should parse empty string

1. expect json as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("\"\"")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_string().unwrap() to_equal ""
```

</details>

#### should parse string with escapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("\"hello\\nworld\"")
expect result.ok.? to_be_true

val json = result.unwrap()
val str = json.as_string().unwrap()
expect str to_contain "hello"
expect str to_contain "world"
```

</details>

#### should parse empty array

1. expect json as array
2. expect json as array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("[]")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_array().? to_be_true
expect json.as_array().unwrap().len() to_equal 0
```

</details>

#### should parse array with elements

1. expect arr len
2. expect arr[0] as number
3. expect arr[1] as number
4. expect arr[2] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect arr len
2. expect arr[0] as array
3. expect arr[1] as array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect json as object
2. expect json as object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse(r"{}")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.as_object().? to_be_true
expect json.as_object().unwrap().len() to_equal 0
```

</details>

#### should parse object with fields

1. expect obj len
2. expect obj["name"] as string
3. expect obj["age"] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect user get


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse("{\"user\": {\"name\": \"Bob\"}}")
expect result.ok.? to_be_true

val json = result.unwrap()
val user = json.get("user").unwrap()
expect user.get("name").unwrap().as_string().unwrap() to_equal "Bob"
```

</details>

#### should fail on invalid JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonValue__parse(r"{invalid")
expect result.err.? to_be_true
```

</details>

#### serialize

#### should serialize null

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Null
val text = json.serialize()
expect text to_equal "null"
```

</details>

#### should serialize boolean

1. expect json serialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Bool(true)
expect json.serialize() to_equal "true"
```

</details>

#### should serialize number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Number(42.0)
val text = json.serialize()
expect text to_contain "42"
```

</details>

#### should serialize string

1. expect json serialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.String("hello")
expect json.serialize() to_equal "\"hello\""
```

</details>

#### should serialize empty array

1. expect json serialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Array([])
expect json.serialize() to_equal "[]"
```

</details>

#### should serialize array

1. JsonValue Number
2. JsonValue Number
3. JsonValue Number


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect json serialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Object({})
expect json.serialize() to_equal "{}"
```

</details>

#### should serialize object

1. "name": JsonValue String
2. "age": JsonValue Number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. "age": JsonValue Number
3. expect text len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. expect name unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Object({
    "name": JsonValue.String("Alice")
})
val name = json.get("name")
expect name.? to_be_true
expect name.unwrap().as_string().unwrap() to_equal "Alice"
```

</details>

#### should return None for missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Object({})
val missing = json.get("missing")
expect missing.? to_be_false
```

</details>

#### should return None for non-object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.String("not an object")
val result = json.get("field")
expect result.? to_be_false
```

</details>

#### get_index

#### should get array element

1. JsonValue String
2. JsonValue String
3. expect first unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Array([])
val result = json.get_index(0)
expect result.? to_be_false
```

</details>

#### should return None for non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.String("not an array")
val result = json.get_index(0)
expect result.? to_be_false
```

</details>

#### type_name

#### should return correct type names

1. expect JsonValue Null  type name
2. expect JsonValue Bool
3. expect JsonValue Number
4. expect JsonValue String
5. expect JsonValue Array
6. expect JsonValue Object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. JsonValue String
2. JsonValue String
3. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Object({})
val path = JsonPath__new("missing.field")
val result = path.query(json)
expect result.? to_be_false
```

</details>

### JsonBuilder

#### construction

#### should build empty object

1. expect json as object


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = JsonBuilder__new()
val json = builder.build()
expect json.as_object().unwrap().len() to_equal 0
```

</details>

#### should build object with fields

1.  put
2.  put
3.  build
4. expect obj len
5. expect obj["name"] as string
6. expect obj["age"] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  put string
2.  build


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonBuilder__new()
    .put_string("name", "Alice")
    .build()

val name = json.get("name").unwrap().as_string().unwrap()
expect name to_equal "Alice"
```

</details>

#### should put number

1.  put number
2.  build


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonBuilder__new()
    .put_number("age", 30.0)
    .build()

val age = json.get("age").unwrap().as_number().unwrap()
expect age to_equal 30.0
```

</details>

#### should put boolean

1.  put bool
2.  build


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonBuilder__new()
    .put_bool("active", true)
    .build()

val active = json.get("active").unwrap().as_bool().unwrap()
expect active to_be_true
```

</details>

#### should put null

1.  put null
2.  build
3. expect value is null


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect json as array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = JsonArray__new()
val json = builder.build()
expect json.as_array().unwrap().len() to_equal 0
```

</details>

#### should build array with elements

1.  push
2.  push
3.  push
4.  build
5. expect arr len
6. expect arr[0] as number
7. expect arr[2] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  push string
2.  build
3. expect arr[0] as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonArray__new()
    .push_string("hello")
    .build()

val arr = json.as_array().unwrap()
expect arr[0].as_string().unwrap() to_equal "hello"
```

</details>

#### should push number

1.  push number
2.  build
3. expect arr[0] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonArray__new()
    .push_number(42.0)
    .build()

val arr = json.as_array().unwrap()
expect arr[0].as_number().unwrap() to_equal 42.0
```

</details>

#### should push boolean

1.  push bool
2.  build
3. expect arr[0] as bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonArray__new()
    .push_bool(true)
    .build()

val arr = json.as_array().unwrap()
expect arr[0].as_bool().unwrap() to_be_true
```

</details>

#### should push null

1.  push null
2.  build
3. expect arr[0] is null


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  put string
2.  put number
3.  build
4. expect json as object


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect json get


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_json("{\"key\": \"value\"}")
expect result.ok.? to_be_true

val json = result.unwrap()
expect json.get("key").unwrap().as_string().unwrap() to_equal "value"
```

</details>

#### to_json_string

#### should serialize to string

1. "key": JsonValue String


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "key": JsonValue String


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.
2.
3. expect obj["name"] as string
4. expect obj["age"] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. JsonValue Number
2. JsonValue Number
3. JsonValue Number
4. expect arr len
5. expect arr[1] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Null
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode boolean

1. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Bool(true)
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode number

1. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Number(42.0)
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode string

1. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.String("hello")
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode array

1. JsonValue Number
2. JsonValue Number
3. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Array([
    JsonValue.Number(1.0),
    JsonValue.Number(2.0)
])
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### should encode object

1. "key": JsonValue String
2. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = JsonValue.Object({
    "key": JsonValue.String("value")
})
val bytes = MsgPack__encode(json)
expect bytes.len() > 0 to_be_true
```

</details>

#### decode

#### should decode encoded data

1. expect decoded unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = JsonValue.Number(42.0)
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes)

expect decoded.? to_be_true
expect decoded.unwrap().as_number().unwrap() to_equal 42.0
```

</details>

#### round-trip

#### should round-trip null

1. expect decoded is null


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = JsonValue.Null
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
expect decoded.is_null() to_be_true
```

</details>

#### should round-trip boolean

1. expect decoded as bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = JsonValue.Bool(true)
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
expect decoded.as_bool().unwrap() to_be_true
```

</details>

#### should round-trip string

1. expect decoded as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = JsonValue.String("hello world")
val bytes = MsgPack__encode(original)
val decoded = MsgPack__decode(bytes).unwrap()
expect decoded.as_string().unwrap() to_equal "hello world"
```

</details>

#### should round-trip array

1. JsonValue Number
2. JsonValue Number
3. JsonValue Number
4. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. "age": JsonValue Number
3. expect obj["name"] as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. "age": JsonValue Number
3. "active": JsonValue Bool
4. JsonValue String
5. JsonValue String
6. expect user get
7. expect user get
8. expect user get
9. expect tags len


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "name": JsonValue String
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  put string
2.  put number
3.  put bool
4.  build


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = JsonArray  new
2. builder = builder push number
3. expect result[0] as number
4. expect result[1] as number
5. expect result[2] as number


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/std/json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
