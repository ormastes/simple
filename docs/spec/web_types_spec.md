# Web Types & HTTP Utilities

*Source: `simple/std_lib/test/features/infrastructure/web_types_spec.spl`*

---

# Web Types & HTTP Utilities

**Feature ID:** #102
**Category:** Infrastructure - Web Framework
**Difficulty:** 2/5
**Status:** Complete

## Overview

The Web Types module provides type-safe HTTP utilities for building web applications
and services. This infrastructure supports Simple's web framework with compile-time
validation of HTTP semantics, fluent response building APIs, and efficient data
representation through bitfields.

Key components:
- **StatusCode:** Type-safe HTTP status code enum (1xx-5xx)
- **ResponseBuilder:** Fluent API for constructing HTTP responses
- **RouteParams:** Type-safe route parameter extraction and parsing
- **Bitfields:** Compact binary data representation
- **TaggedUnions:** Discriminated unions with runtime type tags

## Key Features

- **HTTP Status Codes:** Complete enumeration of standard HTTP status codes
- **Category Methods:** Group codes by category (success, error, redirection)
- **Fluent Response API:** Chain method calls to build responses
- **Route Parameter Extraction:** Parse URL parameters with type conversion
- **Bitfield Types:** Efficient bit-level data access for hardware/protocols
- **Tagged Unions:** Type-safe variant types with runtime discrimination

## Syntax

**HTTP Status Codes:**
```simple
val status = StatusCode.Ok                    # 200
val created = StatusCode.Created              # 201
val not_found = StatusCode.NotFound           # 404
val server_error = StatusCode.InternalServerError  # 500

# Category checking
if status.is_success():
    print("Request succeeded")
```

**Response Builder:**
```simple
# Fluent API
val response = Response.ok()
    .header("Content-Type", "application/json")
    .body("{\"message\": \"Success\"}")
    .build()

# Shorthand methods
val not_found = Response.not_found()
    .body("Page not found")
    .build()
```

**Route Parameters:**
```simple
# Extract from route pattern
val params = RouteParams.from_path("/users/:id", "/users/42")
val user_id = params.get_i64("id")  # 42

# Type conversion
val page = params.get_i64("page")       # Parse as integer
val query = params.get_string("q")      # Get as string
val active = params.get_bool("active")  # Parse as boolean
```

**Bitfields:**
```simple
bitfield StatusReg(u32):
    enabled: 1       # bit 0
    mode: 2          # bits 1-2
    priority: 4      # bits 3-6
    reserved: 25     # bits 7-31

val reg = StatusReg.new(0x12345678)
val is_enabled = reg.enabled()    # Extract bit 0
val mode = reg.mode()              # Extract bits 1-2
```

## Implementation

**Primary Files:**
- `src/type/src/http_status.rs` - HTTP status code enumeration
- `src/type/src/response_builder.rs` - Response builder API
- `src/type/src/route_params.rs` - Route parameter extraction
- `src/type/src/bitfield.rs` - Bitfield type system
- `src/type/src/tagged_union.rs` - Tagged union implementation

**Testing:**
- Unit tests embedded in source files
- Integration tests in web framework

**Dependencies:**
- Standard library only (no external deps)

**Required By:**
- Web framework (planned)
- HTTP server (planned)
- REST API layer (planned)

## HTTP Status Codes

### Categories

HTTP status codes are grouped into five categories:

**1xx - Informational:**
- 100 Continue
- 101 Switching Protocols
- 102 Processing
- 103 Early Hints

**2xx - Success:**
- 200 OK
- 201 Created
- 202 Accepted
- 204 No Content
- 206 Partial Content

**3xx - Redirection:**
- 301 Moved Permanently
- 302 Found
- 303 See Other
- 304 Not Modified
- 307 Temporary Redirect
- 308 Permanent Redirect

**4xx - Client Error:**
- 400 Bad Request
- 401 Unauthorized
- 403 Forbidden
- 404 Not Found
- 405 Method Not Allowed
- 409 Conflict
- 422 Unprocessable Entity
- 429 Too Many Requests

**5xx - Server Error:**
- 500 Internal Server Error
- 501 Not Implemented
- 502 Bad Gateway
- 503 Service Unavailable
- 504 Gateway Timeout

### Category Methods

Each status code has a category:
```simple
val code = StatusCode.Ok
code.category()  # StatusCodeCategory.Success

val code = StatusCode.NotFound
code.category()  # StatusCodeCategory.ClientError
```

### Canonical Reason Phrases

Each status code includes a canonical reason phrase:
```simple
StatusCode.Ok.reason_phrase()              # "OK"
StatusCode.NotFound.reason_phrase()        # "Not Found"
StatusCode.InternalServerError.reason_phrase()  # "Internal Server Error"
```

## Response Builder API

### Fluent Interface

The response builder uses method chaining:
```simple
Response.ok()                              # Start with 200 OK
    .header("Content-Type", "text/plain")  # Add header
    .header("X-Custom", "value")           # Add another header
    .body("Hello, World!")                 # Set body
    .build()                               # Construct final response
```

### Shorthand Constructors

Common status codes have dedicated constructors:
```simple
Response.ok()                    # 200 OK
Response.created()               # 201 Created
Response.no_content()            # 204 No Content
Response.bad_request()           # 400 Bad Request
Response.unauthorized()          # 401 Unauthorized
Response.forbidden()             # 403 Forbidden
Response.not_found()             # 404 Not Found
Response.internal_server_error() # 500 Internal Server Error
Response.service_unavailable()   # 503 Service Unavailable
```

## Route Parameters

### Path Parameters

Extract named parameters from URL paths:
```simple
# Route pattern: /users/:id/posts/:post_id
# Actual path:   /users/42/posts/1337

val params = RouteParams.from_path(pattern, path)
val user_id = params.get_i64("id")        # 42
val post_id = params.get_i64("post_id")   # 1337
```

### Query Parameters

Parse query string parameters:
```simple
# URL: /search?q=simple+lang&page=2&active=true

val params = RouteParams.from_query("q=simple+lang&page=2&active=true")
val query = params.get_string("q")     # "simple lang"
val page = params.get_i64("page")      # 2
val active = params.get_bool("active") # true
```

### Type Conversion

Parameters support automatic type conversion:
```simple
# String parameters
val name = params.get_string("name")

# Integer parameters
val count = params.get_i64("count")

# Float parameters
val price = params.get_f64("price")

# Boolean parameters
val enabled = params.get_bool("enabled")
```

### Error Handling

Parameter access can fail with specific errors:
- **MissingParameter:** Required parameter not present
- **ParseError:** Failed to parse parameter to requested type
- **DuplicateParameter:** Parameter appears multiple times
- **InvalidPattern:** Malformed route pattern

## Bitfield Types

### Compact Data Representation

Bitfields pack multiple values into a single integer:
```simple
bitfield Flags(u8):
    read: 1     # bit 0
    write: 1    # bit 1
    execute: 1  # bit 2
    reserved: 5 # bits 3-7

val perms = Flags.new(0b00000111)  # rwx
val can_read = perms.read()        # true
val can_write = perms.write()      # true
val can_exec = perms.execute()     # true
```

### Backing Types

Bitfields support multiple backing integer types:
- **u8:** 8 bits
- **u16:** 16 bits
- **u32:** 32 bits
- **u64:** 64 bits
- **u128:** 128 bits

### Field Extraction

Access individual fields by name:
```simple
bitfield StatusReg(u32):
    enabled: 1
    mode: 2
    priority: 4

val reg = StatusReg.new(0x0000001F)
val enabled = reg.enabled()     # Extract 1 bit
val mode = reg.mode()           # Extract 2 bits
val priority = reg.priority()   # Extract 4 bits
```

### Use Cases

**Hardware Registers:**
```simple
bitfield ControlReg(u32):
    enable: 1
    interrupt_enable: 1
    dma_mode: 2
    channel: 4
```

**Protocol Headers:**
```simple
bitfield TCPFlags(u8):
    fin: 1
    syn: 1
    rst: 1
    psh: 1
    ack: 1
    urg: 1
```

**Permissions:**
```simple
bitfield Permissions(u16):
    user_read: 1
    user_write: 1
    user_execute: 1
    group_read: 1
    group_write: 1
    group_execute: 1
    other_read: 1
    other_write: 1
    other_execute: 1
```

## Performance Characteristics

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Status code creation | O(1) | Enum variant |
| Category check | O(1) | Match statement |
| Response builder | O(1) per method | Fluent chaining |
| Route param extraction | O(n) | n = path segments |
| Bitfield field access | O(1) | Bit mask and shift |

## Related Features

- Feature #100: Type Inference (validates HTTP types)
- Feature #19: Web Framework (uses these types)
- Feature #27: JSON Serialization (response bodies)

## Language Design Notes

**Type Safety:**
HTTP status codes are type-safe enums, preventing invalid codes:
```simple
val status = StatusCode.Ok  # Valid
val bad = StatusCode.999    # Compile error
```

**Fluent APIs:**
Method chaining creates readable, maintainable code:
```simple
# Clear intent
Response.ok().header("X-Foo", "bar").body("data")

# vs imperative style
val r = Response.new()
r.set_status(200)
r.add_header("X-Foo", "bar")
r.set_body("data")
```

**Bitfield Efficiency:**
Bitfields provide zero-cost abstraction for bit manipulation:
```simple
# High-level API
val enabled = reg.enabled()

# Compiles to
val enabled = (reg.value & 0x1) != 0
```

## HTTP Status Code Enumeration

    StatusCode provides type-safe representation of standard HTTP status codes
    with category classification and reason phrases.

    **Categories:**
    - 1xx: Informational
    - 2xx: Success
    - 3xx: Redirection
    - 4xx: Client Error
    - 5xx: Server Error

    **Implementation:** See `http_status.rs::StatusCode`

**Given** common success scenarios
        **When** selecting appropriate status codes
        **Then** uses 2xx success codes

        **Success Codes:**
        - 200 OK: Standard success response
        - 201 Created: Resource created successfully
        - 202 Accepted: Request accepted for processing
        - 204 No Content: Success with no response body

        **Example:**
        ```simple
        fn create_user(data: UserData) -> Response:
            val user = db.insert(data)
            return Response.created()
                .header("Location", "/users/{user.id}")
                .body(user.to_json())
        ```

        **Verification:** Status code values are correct

**Given** client-side error conditions
        **When** selecting appropriate status codes
        **Then** uses 4xx client error codes

        **Client Error Codes:**
        - 400 Bad Request: Invalid request syntax
        - 401 Unauthorized: Authentication required
        - 403 Forbidden: Insufficient permissions
        - 404 Not Found: Resource doesn't exist
        - 422 Unprocessable Entity: Validation failed

        **Example:**
        ```simple
        fn get_user(id: i64) -> Response:
            match db.find_user(id):
                Some(user) => Response.ok().body(user.to_json())
                None => Response.not_found().body("User not found")
        ```

        **Verification:** Error code values are correct

**Given** server-side error conditions
        **When** selecting appropriate status codes
        **Then** uses 5xx server error codes

        **Server Error Codes:**
        - 500 Internal Server Error: Unexpected error
        - 502 Bad Gateway: Upstream server error
        - 503 Service Unavailable: Temporary outage
        - 504 Gateway Timeout: Upstream timeout

        **Example:**
        ```simple
        fn handle_request(req: Request) -> Response:
            try:
                return process(req)
            catch err:
                log.error(err)
                return Response.internal_server_error()
                    .body("An error occurred")
        ```

        **Verification:** Server error code values are correct

**Given** a status code
        **When** checking its category
        **Then** returns correct category enum

        **Categories:**
        ```simple
        StatusCode.Ok.category()                   # Success
        StatusCode.Created.category()              # Success
        StatusCode.NotFound.category()             # ClientError
        StatusCode.InternalServerError.category()  # ServerError
        ```

        **Category Methods:**
        ```simple
        code.is_informational()  # 1xx
        code.is_success()        # 2xx
        code.is_redirection()    # 3xx
        code.is_client_error()   # 4xx
        code.is_server_error()   # 5xx
        ```

        **Verification:** Category detection works correctly

## HTTP Response Builder

    ResponseBuilder provides a fluent API for constructing HTTP responses
    with headers, status codes, and body content.

    **Fluent Interface:**
    Method chaining creates readable code:
    ```simple
    Response.ok()
        .header("Content-Type", "application/json")
        .body("{}")
        .build()
    ```

    **Implementation:** See `response_builder.rs::ResponseBuilder`

**Given** response requirements
        **When** using builder pattern
        **Then** constructs complete response

        **Example:**
        ```simple
        val response = Response.ok()
            .header("Content-Type", "text/plain")
            .header("X-Request-ID", "abc123")
            .body("Success")
            .build()
        ```

        **Builder Pattern Benefits:**
        - Readable method chaining
        - Type-safe construction
        - Immutable intermediate states
        - Clear intent

        **Verification:** Builder pattern works correctly

**Given** common response scenarios
        **When** using shorthand methods
        **Then** creates appropriate responses

        **Shorthand Methods:**
        ```simple
        Response.ok()                    # 200 OK
        Response.created()               # 201 Created
        Response.no_content()            # 204 No Content
        Response.bad_request()           # 400 Bad Request
        Response.not_found()             # 404 Not Found
        Response.internal_server_error() # 500 Internal Server Error
        ```

        **Example:**
        ```simple
        fn delete_user(id: i64) -> Response:
            db.delete(id)
            return Response.no_content()  # 204, no body needed
        ```

        **Verification:** Shorthand methods set correct status

## Route Parameter Extraction

    RouteParams extracts and parses parameters from URL paths and query strings
    with automatic type conversion and error handling.

    **Path Parameters:**
    Extract from patterns like `/users/:id`

    **Query Parameters:**
    Parse from query strings like `?page=1&size=10`

    **Implementation:** See `route_params.rs::RouteParams`

**Given** a URL path with parameters
        **When** extracting with pattern
        **Then** returns parameter values

        **Example:**
        ```simple
        # Pattern: /users/:id/posts/:post_id
        # Path:    /users/42/posts/1337

        val params = RouteParams.from_path(pattern, path)
        val user_id = params.get_i64("id")        # 42
        val post_id = params.get_i64("post_id")   # 1337
        ```

        **Pattern Matching:**
        - `:name` - Named parameter placeholder
        - Extracts segment values
        - Matches path structure

        **Verification:** Path parameter extraction works

**Given** a query string
        **When** parsing parameters
        **Then** extracts key-value pairs

        **Example:**
        ```simple
        # Query: ?page=2&size=25&sort=name

        val params = RouteParams.from_query("page=2&size=25&sort=name")
        val page = params.get_i64("page")       # 2
        val size = params.get_i64("size")       # 25
        val sort = params.get_string("sort")    # "name"
        ```

        **Query String Format:**
        - Key-value pairs: `key=value`
        - Separator: `&`
        - URL encoding: `%20` for space

        **Verification:** Query parameter parsing works

**Given** string parameter values
        **When** requesting specific types
        **Then** converts and validates types

        **Type Conversion Methods:**
        ```simple
        params.get_string("name")   # String
        params.get_i64("count")     # i64
        params.get_f64("price")     # f64
        params.get_bool("active")   # bool
        ```

        **Conversion Examples:**
        ```simple
        "42" -> i64        # 42
        "3.14" -> f64      # 3.14
        "true" -> bool     # true
        "hello" -> i64     # Error: ParseError
        ```

        **Error Handling:**
        ```simple
        match params.get_i64("invalid"):
            Ok(n) => use_number(n)
            Err(ParseError) => return bad_request()
        ```

        **Verification:** Type conversion works correctly

## Bitfield Data Representation

    Bitfields provide efficient bit-level data access for hardware registers,
    protocol headers, and compact data structures.

    **Syntax:**
    ```simple
    bitfield Name(backing_type):
        field1: bits
        field2: bits
    ```

    **Backing Types:** u8, u16, u32, u64, u128

    **Implementation:** See `bitfield.rs::Bitfield`

**Given** multiple boolean/small values
        **When** using bitfield
        **Then** packs efficiently in single integer

        **Example:**
        ```simple
        bitfield Permissions(u8):
            read: 1      # bit 0
            write: 1     # bit 1
            execute: 1   # bit 2
            reserved: 5  # bits 3-7

        val perms = Permissions.new(0b00000111)  # rwx = 7
        ```

        **Memory Efficiency:**
        - Without bitfield: 3 bools = 3 bytes
        - With bitfield: 1 u8 = 1 byte
        - Space savings: 66%

        **Verification:** Bitfield packing works

**Given** bitfield with multi-bit fields
        **When** extracting field values
        **Then** returns correct values

        **Example:**
        ```simple
        bitfield StatusReg(u32):
            enabled: 1       # bit 0: 0 or 1
            mode: 2          # bits 1-2: 0-3
            priority: 4      # bits 3-6: 0-15
            reserved: 25     # bits 7-31

        val reg = StatusReg.new(0x0000001F)
        val enabled = reg.enabled()     # 1
        val mode = reg.mode()           # 3 (bits 1-2)
        val priority = reg.priority()   # 1 (bits 3-6)
        ```

        **Bit Extraction:**
        ```
        Value: 0x1F = 0b00011111
        enabled (bit 0):     1
        mode (bits 1-2):     11 (3)
        priority (bits 3-6): 0001 (1)
        ```

        **Verification:** Multi-bit field extraction works

**Given** various bit width requirements
        **When** choosing backing type
        **Then** selects appropriate size

        **Backing Type Selection:**
        ```simple
        bitfield Small(u8):      # 8 bits max
            flags: 8

        bitfield Medium(u16):    # 16 bits max
            fields: 16

        bitfield Large(u32):     # 32 bits max
            config: 32

        bitfield Huge(u64):      # 64 bits max
            register: 64

        bitfield Massive(u128):  # 128 bits max
            data: 128
        ```

        **Type Selection Guidelines:**
        - u8: Simple flags (8 bits)
        - u16: Small registers (16 bits)
        - u32: Hardware registers (32 bits)
        - u64: Large registers (64 bits)
        - u128: Crypto/hash values (128 bits)

        **Verification:** Backing types have correct sizes
