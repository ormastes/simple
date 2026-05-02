# Trait-Based Standard Library Design

## Overview

This document outlines how to apply Rust-style trait patterns extensively to Simple's standard library for better abstraction, code reuse, and API consistency.

## Key Rust Trait Patterns to Apply

### 1. I/O Traits

**Read Trait** - For types that can be read from:
```simple
trait Read:
    fn read(self, buf: &mut [u8]) -> Result[usize, IoError]

    # Default implementations
    fn read_exact(self, buf: &mut [u8]) -> Result[(), IoError]:
        # Read until buf is filled or error

    fn read_to_end(self, buf: &mut Array[u8]) -> Result[usize, IoError]:
        # Read until EOF

    fn read_to_string(self, s: &mut String) -> Result[usize, IoError]:
        # Read UTF-8 to string
```

**Write Trait** - For types that can be written to:
```simple
trait Write:
    fn write(self, buf: &[u8]) -> Result[usize, IoError]
    fn flush(self) -> Result[(), IoError]

    # Default implementations
    fn write_all(self, buf: &[u8]) -> Result[(), IoError]:
        # Write until all bytes written

    fn write_fmt(self, fmt: str) -> Result[(), IoError]:
        # Write formatted string
```

**Seek Trait** - For types that support seeking:
```simple
trait Seek:
    fn seek(self, pos: SeekFrom) -> Result[u64, IoError]

    # Default implementations
    fn rewind(self) -> Result[(), IoError]:
        self.seek(SeekFrom::Start(0)).map(|_| ())

    fn stream_position(self) -> Result[u64, IoError]:
        self.seek(SeekFrom::Current(0))
```

**BufRead Trait** - For buffered reading:
```simple
trait BufRead: Read:
    fn fill_buf(self) -> Result[&[u8], IoError]
    fn consume(self, amt: usize)

    # Default implementations
    fn read_line(self, buf: &mut String) -> Result[usize, IoError]
    fn lines(self) -> Lines[Self]
```

### 2. Collection Traits

**Extend Trait** - Extend collection with items:
```simple
trait Extend[A]:
    fn extend[I: IntoIterator[Item=A]](self, iter: I)
```

**Collect Trait Pattern** - Already exists as FromIterator:
```simple
trait FromIterator[A]:
    fn from_iter[I: IntoIterator[Item=A]](iter: I) -> Self
```

**AsSlice/AsMutSlice** - View as slice:
```simple
trait AsSlice[T]:
    fn as_slice(self) -> &[T]

trait AsMutSlice[T]:
    fn as_mut_slice(self) -> &mut [T]
```

### 3. Conversion Traits (Enhance Existing)

**AsRef/AsMut** - Cheap reference conversions:
```simple
trait AsRef[T]:
    fn as_ref(self) -> &T

trait AsMut[T]:
    fn as_mut(self) -> &mut T
```

**Borrow/BorrowMut** - For types that can be borrowed:
```simple
trait Borrow[Borrowed]:
    fn borrow(self) -> &Borrowed

trait BorrowMut[Borrowed]: Borrow[Borrowed]:
    fn borrow_mut(self) -> &mut Borrowed
```

**ToOwned** - Create owned copy:
```simple
trait ToOwned:
    type Owned
    fn to_owned(self) -> Self::Owned
```

### 4. Error Handling Traits

**Error Trait** - Base error trait:
```simple
trait Error: Display:
    fn source(self) -> Option[&Error]:
        None

    fn description(self) -> str:
        self.to_string()
```

### 5. String Traits

**ToString** - Convert to string (derive from Display):
```simple
trait ToString:
    fn to_string(self) -> String
```

**FromStr** - Parse from string:
```simple
trait FromStr:
    type Err
    fn from_str(s: &str) -> Result[Self, Self::Err]
```

## Implementation Plan

### Phase 1: Core I/O Traits

Add to `lib/std/core/traits.spl`:

1. `Read` trait
2. `Write` trait
3. `Seek` trait
4. `SeekFrom` enum
5. `BufRead` trait

Implement on:
- `File` (async_nogc_mut/io/fs.spl)
- `FileReader`/`FileWriter` (async_gc_immut/io/fs.spl)
- `TcpStream` (net/tcp.spl)
- `UdpSocket` (net/udp.spl)
- `Buffer`/`BufReader`/`BufWriter` (io/buf.spl)
- `Terminal` (io/term.spl)

### Phase 2: Collection Traits

Add to `lib/std/core/traits.spl`:

1. `Extend` trait
2. `AsSlice`/`AsMutSlice` traits
3. `Len` trait (common interface)

Implement on:
- `Vec`, `Array`
- `String`
- `FixedVec`, `StaticVec`
- `FixedString`, `StaticString`
- `Dict`, `Set`

### Phase 3: Enhanced Conversion Traits

Enhance existing traits:
1. Add `Borrow`/`BorrowMut`
2. Add `ToOwned`
3. Add `FromStr`
4. Add `Error` trait

### Phase 4: Iterator Enhancements

Add to existing Iterator:
1. `DoubleEndedIterator` trait
2. `ExactSizeIterator` trait
3. Additional default methods

## Trait Implementation Examples

### File implementing Read/Write/Seek

```simple
# In async_nogc_mut/io/fs.spl

impl Read for File:
    fn read(self, buf: &mut [u8]) -> Result[usize, IoError]:
        native_file_read(self.handle, buf, buf.len())

impl Write for File:
    fn write(self, buf: &[u8]) -> Result[usize, IoError]:
        native_file_write(self.handle, buf, buf.len())

    fn flush(self) -> Result[(), IoError]:
        native_file_flush(self.handle)

impl Seek for File:
    fn seek(self, pos: SeekFrom) -> Result[u64, IoError]:
        native_file_seek(self.handle, pos)
```

### Vec implementing Extend

```simple
impl Extend[T] for Vec[T]:
    fn extend[I: IntoIterator[Item=T]](self, iter: I):
        for item in iter:
            self.push(item)
```

### StaticVec implementing AsSlice

```simple
impl AsSlice[T] for StaticVec[T, const N: usize]:
    fn as_slice(self) -> &[T]:
        &self.data[0..self.len]
```

### String implementing Borrow

```simple
impl Borrow[str] for String:
    fn borrow(self) -> &str:
        self.as_str()
```

## Benefits of Trait-Based Design

1. **Polymorphism**: Functions can accept any type implementing a trait
   ```simple
   fn copy_to[R: Read, W: Write](reader: &R, writer: &mut W) -> Result[u64, IoError]
   ```

2. **Code Reuse**: Default implementations reduce boilerplate

3. **Consistency**: Same interface across different types

4. **Extensibility**: Users can implement traits for custom types

5. **Discoverability**: Traits document capabilities

## Blanket Implementations

```simple
# Any Read can be buffered
impl[R: Read] BufReader[R]:
    fn new(reader: R) -> BufReader[R]

# Any Iterator can collect
impl[T, I: Iterator[Item=T], C: FromIterator[T]] for I:
    fn collect(self) -> C:
        C::from_iter(self)

# Any Display can be converted to String
impl[T: Display] ToString for T:
    fn to_string(self) -> String:
        # format via Display
```

## Comparison: Existing vs Enhanced

| Type | Current Methods | With Traits |
|------|-----------------|-------------|
| File | read(), write(), seek() | impl Read, Write, Seek |
| Vec | push(), pop(), len() | impl Extend, AsSlice, IntoIterator |
| String | push_str(), as_str() | impl Borrow[str], AsRef[str], Write |
| TcpStream | send(), recv() | impl Read, Write |

## Migration Notes

1. Existing methods remain - traits add polymorphic interface
2. Trait methods can delegate to existing implementations
3. No breaking changes to existing code
4. Gradually add trait impls to stdlib types
