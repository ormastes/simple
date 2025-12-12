# Stdlib Interface Inconsistencies - Temporary Analysis Document

> **Status: COMPLETED** - All high and medium priority issues have been fixed.

## Fixes Applied

### Fixed Files:
1. `lib/std/host/async_nogc_mut/io/fs.spl` - Changed `from`/`to` to `src`/`dst` in rename/copy
2. `lib/std/host/async_nogc_mut/net/http.spl` - Changed `to_str()` to `as_str()`
3. `lib/std/core_nogc_immut/static_vec.spl` - Added missing methods, error type, type aliases, fixed field names
4. `lib/std/core_nogc_immut/static_string.spl` - Added missing methods, error type, type aliases, fixed field names
5. `lib/std/host/async_gc_immut/io/term.spl` - Added missing terminal functions (cursor, screen, keyboard)

---

## 1. Naming Inconsistencies

### 1.1 Function/Method Name Variations

| Location | Current | Should Be | Reason |
|----------|---------|-----------|--------|
| `async_nogc_mut/io/fs.spl:153` | `rename(from, to)` | `rename(src, dst)` | Consistency with copy(), other file ops |
| `async_nogc_mut/io/fs.spl:157` | `copy(from, to)` | `copy(src, dst)` | `from` is a reserved keyword in Simple |
| `async_nogc_mut/net/http.spl:22` | `HttpMethod::to_str()` | `HttpMethod::as_str()` | Consistency with other `as_*` methods |
| `async_gc_immut/net/http.spl:23` | `HttpMethod::as_str()` | Already correct | (reference) |
| `async_nogc_mut/io/term.spl:76` | `write_err()` | `write_stderr()` or `ewrite()` | Consistency with print/eprint pattern |

### 1.2 Type Name Inconsistencies

| Location | Current | Should Be | Reason |
|----------|---------|-----------|--------|
| `core_nogc/fixed_vec.spl` | `const N: u64` | `const N: usize` | Consistency with static_vec |
| `core_nogc_immut/static_vec.spl` | `const N: usize` | (reference) | Standard size type |
| `core_nogc/fixed_string.spl` | `const N: u64` | `const N: usize` | Consistency |
| `core_nogc_immut/static_string.spl` | `const N: usize` | (reference) | Standard size type |

### 1.3 Field Name Inconsistencies

| Location | Current | Should Be | Reason |
|----------|---------|-----------|--------|
| `core_nogc_immut/static_vec.spl` | `_data`, `_len` | `data`, `len` | Consistency with fixed_vec (no underscore prefix) |
| `core_nogc_immut/static_string.spl` | `_data`, `_len` | `data`, `len` | Consistency with fixed_string |

## 2. Argument Order Inconsistencies

### 2.1 File Operations

| Function | async_nogc_mut | async_gc_immut | Recommended |
|----------|----------------|----------------|-------------|
| `rename` | `(from, to)` | `(src, dst)` | `(src, dst)` |
| `copy` | `(from, to)` | `(src, dst)` | `(src, dst)` |

### 2.2 Network send/recv

| Type | Operation | Current | Note |
|------|-----------|---------|------|
| TCP | `send_to` | N/A (TCP is connected) | OK |
| UDP | `send_to(data, addr)` | `(data, addr)` | OK |
| UDP | `recv_from(buf)` | `(buf)` returns `(count, addr)` | OK |

## 3. Missing Functions Across Variants

### 3.1 async_gc_immut Missing (compared to async_nogc_mut)

| Module | Missing Functions |
|--------|-------------------|
| `io/fs.spl` | `read_text`, `write_text`, `append_text` convenience wrappers need immutable pattern |
| `io/term.spl` | Missing: `clear`, `clear_line`, `move_to`, `move_up/down/left/right`, `hide_cursor`, `show_cursor`, `save_cursor`, `restore_cursor`, `cursor_position`, `set_title`, `bell`, `read_key`, `KeyEvent`, `KeyCode`, `KeyModifiers`, most cursor operations |
| `io/buf.spl` | Missing: `BufReader`, `BufWriter`, `LineWriter` (only have immutable Buffer variants) |
| `net/tcp.spl` | Missing: `TcpListener` struct, `connect_timeout`, `read_exact`, `write_all`, `shutdown`, `peek`, socket options |
| `net/udp.spl` | Missing: `bind_any`, `recv/send` (connected), `peek`, `peek_from`, socket options, multicast |
| `net/http.spl` | Missing: `HttpClient` struct, most builder methods, full header support |
| `net/ftp.spl` | Entire module missing |

### 3.2 Static String Missing Methods (compared to FixedString)

| Method | FixedString | StaticString | Action |
|--------|-------------|--------------|--------|
| `from_str_truncate` | Yes | No | Add |
| `is_full` | Yes | No | Add |
| `remaining` | Yes | No | Add |
| `push_byte` | Yes | No | Add (as returning Option) |
| `push_str` | Yes | No (`concat` instead) | Add for consistency |
| `pop_byte` | Yes | No | Add (returning tuple) |
| `clear` | Yes | No | Add as `cleared()` |
| `truncate` | Yes | No | Add as `truncated(len)` |
| `byte_at` | Yes | No | Add |
| `starts_with` | Yes | No | Add |
| `ends_with` | Yes | No | Add |
| `contains` | Yes | No | Add |
| `find` | Yes | No | Add |
| `eq` | Yes | No | Add |
| `trim` | Yes | No | Add (returning new string) |
| `to_uppercase` | Yes | No | Add as `uppercased()` |
| `to_lowercase` | Yes | No | Add as `lowercased()` |
| Error type | `FixedStringError` | No | Add `StaticStringError` |
| Type aliases | Yes | No | Add |

### 3.3 Static Vec Missing Methods (compared to FixedVec)

| Method | FixedVec | StaticVec | Action |
|--------|----------|-----------|--------|
| `from_array` | Yes | Yes | OK |
| `remaining` | Yes | No | Add |
| `try_push` | Yes | No | Add returning Result |
| `get_mut` | Yes | N/A | (immutable - not applicable) |
| `index` | Yes | No | Add |
| `index_mut` | Yes | N/A | (immutable) |
| `first` | Yes | No | Add |
| `last` | Yes | No | Add |
| `clear` | Yes | No | Add as `cleared()` |
| `truncate` | Yes | No | Add as `truncated(len)` |
| `insert` | Yes | No | Add as `inserted(idx, val)` |
| `remove` | Yes | No | Add returning `Option[(T, Self)]` |
| `swap_remove` | Yes | No | Add returning `Option[(T, Self)]` |
| `retain` | Yes | No | Add as `filtered(pred)` |
| `find` | Yes | No | Add |
| `contains` | Yes | No | Add |
| `as_slice` | Yes | No | Add |
| `extend_from_slice` | Yes | No | Add as `extended(slice)` |
| `sort` | Yes | No | Add as `sorted()` |
| `reverse` | Yes | No | Add as `reversed()` |
| Error type | `FixedVecError` | No | Add `StaticVecError` |
| Type aliases | Yes | No | Add |

## 4. Return Type Inconsistencies

### 4.1 Error Type Usage

| Module | Error Type | Consistent? |
|--------|------------|-------------|
| `io/fs.spl` | `IoError` | Yes |
| `io/term.spl` (nogc_mut) | `TermError` | Different from IoError |
| `io/term.spl` (gc_immut) | Uses `IoError` inconsistently | Should use TermError |
| `net/tcp.spl` | `IoError` | Yes |
| `net/udp.spl` | `IoError` | Yes |
| `net/http.spl` | `HttpError` | Yes (specific) |

### 4.2 Success Return Values

| Operation | async_nogc_mut | async_gc_immut | Note |
|-----------|----------------|----------------|------|
| `write` | `Result[ByteCount, IoError]` | `Result[ByteCount, IoError]` | OK |
| `read` (file) | `Result[ByteCount, IoError]` | `Result[(Bytes, FileReader), IoError]` | Immutable returns new state |

## 5. Priority Fixes

### High Priority (Breaking API differences)
1. Fix `from`/`to` -> `src`/`dst` in rename/copy (reserved keyword issue)
2. Add missing functions to async_gc_immut/io/term.spl
3. Standardize const type parameter to `usize` across all collections

### Medium Priority (Missing functionality)
1. Add missing methods to StaticVec and StaticString
2. Add missing type aliases
3. Add BufReader/BufWriter equivalents for immutable variant

### Low Priority (Cosmetic)
1. Standardize field naming (remove underscore prefix)
2. Standardize `to_str` -> `as_str` naming
3. Add missing FTP module to async_gc_immut

## 6. Files to Modify

1. `lib/std/host/async_nogc_mut/io/fs.spl` - Fix rename/copy param names
2. `lib/std/host/async_nogc_mut/net/http.spl` - Fix `to_str` -> `as_str`
3. `lib/std/host/async_gc_immut/io/fs.spl` - Already uses `src`/`dst` (good)
4. `lib/std/host/async_gc_immut/io/term.spl` - Add missing terminal functions
5. `lib/std/core_nogc/fixed_vec.spl` - Change `u64` -> `usize`
6. `lib/std/core_nogc/fixed_string.spl` - Change `u64` -> `usize`
7. `lib/std/core_nogc_immut/static_vec.spl` - Add missing methods, fix field names
8. `lib/std/core_nogc_immut/static_string.spl` - Add missing methods, fix field names
