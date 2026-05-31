# Node Api Conformance Specification

## Scenarios

### Node.js path module

### path.dirname

#### gets directory name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_dirname([JsValue.String(v: "/usr/local/bin/node")]))).to_equal("/usr/local/bin")
```

</details>

#### root path

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_dirname([JsValue.String(v: "/file")]))).to_equal("/")
```

</details>

#### no slash

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_dirname([JsValue.String(v: "file.js")]))).to_equal(".")
```

</details>

### path.basename

#### gets base name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_basename([JsValue.String(v: "/usr/local/bin/node")]))).to_equal("node")
```

</details>

#### strips extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_basename([JsValue.String(v: "/path/file.js"), JsValue.String(v: ".js")]))).to_equal("file")
```

</details>

### path.extname

#### gets extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_extname([JsValue.String(v: "file.js")]))).to_equal(".js")
```

</details>

#### no extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_extname([JsValue.String(v: "file")]))).to_equal("")
```

</details>

#### multiple dots

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_extname([JsValue.String(v: "archive.tar.gz")]))).to_equal(".gz")
```

</details>

### path.isAbsolute

#### absolute

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_isAbsolute([JsValue.String(v: "/usr/bin")]))).to_equal("true")
```

</details>

#### relative

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_isAbsolute([JsValue.String(v: "src/main.js")]))).to_equal("false")
```

</details>

### path.join

#### joins paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_join([JsValue.String(v: "/usr"), JsValue.String(v: "local"), JsValue.String(v: "bin")]))).to_equal("/usr/local/bin")
```

</details>

#### normalizes joined paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_join([JsValue.String(v: "/usr/"), JsValue.String(v: "./local"), JsValue.String(v: "../bin")]))).to_equal("/usr/bin")
```

</details>

#### preserves trailing separator like path.posix.join

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_join([JsValue.String(v: "/foo/"), JsValue.String(v: "bar/")]))).to_equal("/foo/bar/")
```

</details>

### path.normalize

#### removes dot and dotdot segments

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "foo/../bar/./baz")]))).to_equal("bar/baz")
```

</details>

#### preserves root for absolute paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "/foo/../bar")]))).to_equal("/bar")
```

</details>

#### preserves trailing separator like path.posix.normalize

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "foo//bar//")]))).to_equal("foo/bar/")
```

</details>

#### preserves trailing separator for normalized relative dot result

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "foo/..//")]))).to_equal("./")
```

</details>

### Node.js process module

### process identity

#### returns a stable Node-like platform

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_platform([]))).to_equal("linux")
```

</details>

#### returns a stable Node-like architecture

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_arch([]))).to_equal("x64")
```

</details>

#### returns a version-shaped string

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_version([]))).to_start_with("v")
```

</details>

### process versions and release

#### returns deterministic process.versions.node

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_versions_node([]))).to_equal("0.0.0-simple")
```

</details>

#### returns deterministic process.versions.v8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_versions_v8([]))).to_equal("simple-js")
```

</details>

#### keeps libuv version typed unavailable until scheduler parity exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_versions_uv([]))).to_equal("unavailable")
```

</details>

#### returns a Node-compatible release name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_release_name([]))).to_equal("node")
```

</details>

#### does not fake release source URLs

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_release_sourceUrl([]))).to_equal("undefined")
```

</details>

#### reports non-LTS for the deterministic Simple compatibility profile

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_release_lts([]))).to_equal("false")
```

</details>

### process working directory and argv

#### uses deterministic cwd when host cwd is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_cwd([]))).to_equal("/")
```

</details>

#### returns a deterministic argv shape

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = process_argv([])
expect(argv.len()).to_equal(2)
expect(argv[0]).to_equal("simple")
expect(argv[1]).to_equal("")
```

</details>

### process env

#### does not expose ambient host environment

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_env_get([JsValue.String(v: "PATH")]))).to_equal("undefined")
```

</details>

#### keeps missing env keys typed as unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_env_get([JsValue.String(v: "")]))).to_equal("undefined")
```

</details>

### process.nextTick

#### is typed unavailable without runtime scheduler support

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_nextTick([]))).to_equal("undefined")
```

</details>

### Node.js os module

### deterministic os identity

#### returns stable os.platform

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_platform([]))).to_equal("linux")
```

</details>

#### returns stable os.arch

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_arch([]))).to_equal("x64")
```

</details>

#### returns stable os.type

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_type([]))).to_equal("Linux")
```

</details>

#### returns stable os.release

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_release([]))).to_equal("0.0.0-simple")
```

</details>

#### keeps homedir deterministic without leaking host users

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_homedir([]))).to_equal("/")
```

</details>

#### keeps tmpdir deterministic without leaking host paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_tmpdir([]))).to_equal("/tmp")
```

</details>

### Node.js Buffer module

### Buffer.byteLength

#### counts utf8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_byteLength([JsValue.String(v: "hello"), JsValue.String(v: "utf8")]))).to_equal("5")
```

</details>

#### counts hex decoded bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_byteLength([JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex")]))).to_equal("5")
```

</details>

#### counts base64 decoded bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_byteLength([JsValue.String(v: "aGVsbG8="), JsValue.String(v: "base64")]))).to_equal("5")
```

</details>

### Buffer.from(...).toString(...)

#### encodes utf8 input as hex

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "hello"), JsValue.String(v: "utf8"), JsValue.String(v: "hex")]))).to_equal("68656c6c6f")
```

</details>

#### decodes hex input as utf8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex"), JsValue.String(v: "utf8")]))).to_equal("hello")
```

</details>

#### round trips base64 input to utf8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "aGVsbG8="), JsValue.String(v: "base64"), JsValue.String(v: "utf8")]))).to_equal("hello")
```

</details>

#### encodes utf8 input as base64

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "hello"), JsValue.String(v: "utf8"), JsValue.String(v: "base64")]))).to_equal("aGVsbG8=")
```

</details>

### Buffer.concat

#### concatenates byte buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_concat_toString([JsValue.String(v: "6865"), JsValue.String(v: "hex"), JsValue.String(v: "6c6c6f"), JsValue.String(v: "hex"), JsValue.String(v: "utf8")]))).to_equal("hello")
```

</details>

### NodeBuffer value semantics

#### compares exact byte contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = NodeBuffer.from_text("68656c6c6f", "hex")
val right = NodeBuffer.from_text("hello", "utf8")
expect(left.equals(right)).to_equal(true)
expect(left.length()).to_equal(5)
```

</details>

### Node.js runtime shape

### JSON.parse host path

#### parses JSON objects through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('{\"ok\":true,\"name\":\"simple\"}').ok")).to_equal("true")
```

</details>

#### parses JSON object string properties through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('{\"ok\":true,\"name\":\"simple\"}').name")).to_equal("simple")
```

</details>

#### parses JSON arrays through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('[1,2,3]').length")).to_equal("3")
```

</details>

#### parses JSON array indexes through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('[1,2,3]')[1]")).to_equal("2")
```

</details>

#### rejects malformed JSON before JS allocation

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('{\"ok\":true,}')")).to_equal("error")
```

</details>

### require builtins

#### resolves node:path through deterministic require

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('node:path').join('/usr', 'local', '..', 'bin')")).to_equal("/usr/bin")
```

</details>

#### resolves path alias through deterministic require

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('path').basename('/tmp/simple.js')")).to_equal("simple.js")
```

</details>

#### exposes the POSIX path namespace through require

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('node:path').posix.normalize('foo//bar//')")).to_equal("foo/bar/")
expect(_eval_str("require('path').posix.join('/foo/', 'bar/')")).to_equal("/foo/bar/")
```

</details>

#### marks unsupported builtin modules denied

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('fs').status")).to_equal("denied")
```

</details>

#### resolves os and node:os through deterministic require

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('os').platform()")).to_equal("linux")
expect(_eval_str("require('node:os').arch()")).to_equal("x64")
expect(_eval_str("require('os').type()")).to_equal("Linux")
expect(_eval_str("require('node:os').type()")).to_equal("Linux")
expect(_eval_str("require('os').release()")).to_equal("0.0.0-simple")
expect(_eval_str("require('node:os').release()")).to_equal("0.0.0-simple")
expect(_eval_str("require('os').homedir()")).to_equal("/")
expect(_eval_str("require('node:os').homedir()")).to_equal("/")
expect(_eval_str("require('node:os').tmpdir()")).to_equal("/tmp")
```

</details>

### Buffer global and module shape

#### exposes Buffer through require('buffer')

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.from('68656c6c6f', 'hex').toString('utf8')")).to_equal("hello")
```

</details>

#### builds buffers from numeric byte arrays

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.from([104,101,108,108,111]).toString('utf8')")).to_equal("hello")
```

</details>

#### normalizes numeric array bytes like Node buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,255,256,-1]).toString('hex')")).to_equal("0061ff00ff")
```

</details>

#### compares lower buffers before higher buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.compare(Buffer.from('61', 'hex'), Buffer.from('62', 'hex'))")).to_equal("-1")
```

</details>

#### compares higher buffers after lower buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.compare(require('buffer').Buffer.from('62', 'hex'), require('buffer').Buffer.from('61', 'hex'))")).to_equal("1")
```

</details>

#### compares identical buffers equally

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.compare(Buffer.from('6162', 'hex'), Buffer.from('6162', 'hex'))")).to_equal("0")
```

</details>

#### checks equal buffer contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('6162', 'hex').equals(Buffer.from('6162', 'hex'))")).to_equal("true")
```

</details>

#### checks unequal buffer contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('6162', 'hex').equals(Buffer.from('6163', 'hex'))")).to_equal("false")
```

</details>

#### slices buffer byte ranges

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').slice(1, 4).toString('utf8')")).to_equal("ell")
```

</details>

#### slices with negative and clamped indexes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').slice(-2, 99).toString('hex')")).to_equal("6c6f")
```

</details>

#### subarrays buffer byte ranges

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').subarray(1, 4).toString('utf8')")).to_equal("ell")
```

</details>

#### subarrays with negative start

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').subarray(-2).toString('hex')")).to_equal("6c6f")
```

</details>

#### reads unsigned bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,255]).readUInt8(1)")).to_equal("97")
```

</details>

#### bounds out-of-range unsigned byte reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,255]).readUInt8(99)")).to_equal("0")
```

</details>

#### reads little-endian unsigned 16-bit values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([52,18,86,120]).readUInt16LE(0)")).to_equal("4660")
```

</details>

#### reads big-endian unsigned 16-bit values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([52,18,86,120]).readUInt16BE(2)")).to_equal("22136")
```

</details>

#### bounds out-of-range unsigned 16-bit reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([52]).readUInt16LE(0)")).to_equal("0")
```

</details>

#### reads WASM magic as little-endian u32

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,115,109,1,0,0,0]).readUInt32LE(0)")).to_equal("1836278016")
```

</details>

#### reads WASM version as little-endian u32

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,115,109,1,0,0,0]).readUInt32LE(4)")).to_equal("1")
```

</details>

#### reads big-endian unsigned 32-bit values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,115,109,1,0,0,0]).readUInt32BE(0)")).to_equal("6388590")
```

</details>

#### bounds out-of-range unsigned 32-bit big-endian reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([1,2,3]).readUInt32BE(0)")).to_equal("0")
```

</details>

#### writes unsigned bytes and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(2).writeUInt8(255, 1)")).to_equal("2")
```

</details>

#### writes little-endian unsigned 16-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(2).writeUInt16LE(4660, 0)")).to_equal("2")
```

</details>

#### writes big-endian unsigned 16-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(2).writeUInt16BE(4660, 0)")).to_equal("2")
```

</details>

#### writes little-endian unsigned 32-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(4).writeUInt32LE(1836278016, 0)")).to_equal("4")
```

</details>

#### writes big-endian unsigned 32-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(4).writeUInt32BE(6388590, 0)")).to_equal("4")
```

</details>

#### exposes Buffer.concat through require('buffer')

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.concat([require('buffer').Buffer.from('6865', 'hex'), require('buffer').Buffer.from('6c6c6f', 'hex')]).toString('utf8')")).to_equal("hello")
```

</details>

#### allocates zero-filled buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(3).toString('hex')")).to_equal("000000")
```

</details>

#### allocates filled buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.alloc(4, 97).toString('utf8')")).to_equal("aaaa")
```

</details>

#### identifies bounded Buffer instances

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.isBuffer(require('buffer').Buffer.from('68656c6c6f', 'hex'))")).to_equal("true")
```

</details>

#### rejects non-buffer values for Buffer.isBuffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.isBuffer('hello')")).to_equal("false")
```

</details>

#### exposes Buffer through globalThis

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("globalThis.Buffer.byteLength('hello', 'utf8')")).to_equal("5")
```

</details>

### process global shape

#### exposes deterministic process cwd

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.cwd()")).to_equal("/")
```

</details>

#### denies ambient process env values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof process.env.PATH")).to_equal("undefined")
```

</details>

#### exposes deterministic process versions

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.versions.node")).to_equal("0.0.0-simple")
```

</details>

#### exposes deterministic process argv length

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.argv.length")).to_equal("2")
```

</details>

#### exposes deterministic process argv executable

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.argv[0]")).to_equal("simple")
```

</details>

#### exposes deterministic require process argv

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('process').argv.length")).to_equal("2")
```

</details>

### TextEncoder and TextDecoder globals

#### encodes text to Uint8Array-compatible bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("new TextEncoder().encode('hello').length")).to_equal("5")
expect(_eval_str("new TextEncoder().encode('hello')[1]")).to_equal("101")
```

</details>

#### decodes Uint8Array-compatible bytes as UTF-8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("new TextDecoder().decode(new Uint8Array([104,101,108,108,111]))")).to_equal("hello")
```

</details>

#### reports deterministic UTF-8 labels

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("new TextEncoder().encoding")).to_equal("utf-8")
expect(_eval_str("new TextDecoder('utf8').encoding")).to_equal("utf-8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/js/node_api_conformance_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Node.js path module
- path.dirname
- path.basename
- path.extname
- path.isAbsolute
- path.join
- path.normalize
- Node.js process module
- process identity
- process versions and release
- process working directory and argv
- process env
- process.nextTick
- Node.js os module
- deterministic os identity
- Node.js Buffer module
- Buffer.byteLength
- Buffer.from(...).toString(...)
- Buffer.concat
- NodeBuffer value semantics
- Node.js runtime shape
- JSON.parse host path
- require builtins
- Buffer global and module shape
- process global shape
- TextEncoder and TextDecoder globals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 97 |
| Active scenarios | 97 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

