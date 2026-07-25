# Python Helper Methods - Comprehensive Inventory

## 1. Text/String Methods

### 1.1 str Instance Methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `capitalize()` | Return string with first character capitalized and rest lowercased | Case |
| 2 | `casefold()` | Return casefolded (aggressive lowercase) copy for caseless matching | Case |
| 3 | `center(width, fillchar=' ')` | Return centered string padded to given width | Alignment |
| 4 | `count(sub, start, end)` | Count non-overlapping occurrences of substring | Search |
| 5 | `encode(encoding='utf-8', errors='strict')` | Encode string to bytes using given encoding | Encoding |
| 6 | `endswith(suffix, start, end)` | Return True if string ends with the given suffix | Test |
| 7 | `expandtabs(tabsize=8)` | Replace tab characters with spaces | Whitespace |
| 8 | `find(sub, start, end)` | Return lowest index of substring, or -1 if not found | Search |
| 9 | `format(*args, **kwargs)` | Perform string formatting with positional/keyword arguments | Formatting |
| 10 | `format_map(mapping)` | Format string using a mapping (dict subclass friendly) | Formatting |
| 11 | `index(sub, start, end)` | Like find() but raises ValueError if substring not found | Search |
| 12 | `isalnum()` | Return True if all characters are alphanumeric | Test |
| 13 | `isalpha()` | Return True if all characters are alphabetic | Test |
| 14 | `isascii()` | Return True if all characters are ASCII (U+0000..U+007F) | Test |
| 15 | `isdecimal()` | Return True if all characters are decimal characters | Test |
| 16 | `isdigit()` | Return True if all characters are digits | Test |
| 17 | `isidentifier()` | Return True if string is a valid Python identifier | Test |
| 18 | `islower()` | Return True if all cased characters are lowercase | Test |
| 19 | `isnumeric()` | Return True if all characters are numeric characters | Test |
| 20 | `isprintable()` | Return True if all characters are printable | Test |
| 21 | `isspace()` | Return True if all characters are whitespace | Test |
| 22 | `istitle()` | Return True if string is titlecased | Test |
| 23 | `isupper()` | Return True if all cased characters are uppercase | Test |
| 24 | `join(iterable)` | Concatenate iterable of strings with self as separator | Join/Split |
| 25 | `ljust(width, fillchar=' ')` | Return left-justified string padded to given width | Alignment |
| 26 | `lower()` | Return lowercased copy of the string | Case |
| 27 | `lstrip(chars=None)` | Return string with leading characters removed | Strip |
| 28 | `maketrans(x, y=None, z=None)` | Return a translation table for use with translate() | Transform |
| 29 | `partition(sep)` | Split at first occurrence of sep, return (before, sep, after) | Join/Split |
| 30 | `removeprefix(prefix)` | Remove the specified prefix if present (Python 3.9+) | Strip |
| 31 | `removesuffix(suffix)` | Remove the specified suffix if present (Python 3.9+) | Strip |
| 32 | `replace(old, new, count=-1)` | Return string with occurrences of old replaced by new | Transform |
| 33 | `rfind(sub, start, end)` | Return highest index of substring, or -1 if not found | Search |
| 34 | `rindex(sub, start, end)` | Like rfind() but raises ValueError if substring not found | Search |
| 35 | `rjust(width, fillchar=' ')` | Return right-justified string padded to given width | Alignment |
| 36 | `rpartition(sep)` | Split at last occurrence of sep, return (before, sep, after) | Join/Split |
| 37 | `rsplit(sep=None, maxsplit=-1)` | Split from the right, return list of substrings | Join/Split |
| 38 | `rstrip(chars=None)` | Return string with trailing characters removed | Strip |
| 39 | `split(sep=None, maxsplit=-1)` | Split string by separator, return list of substrings | Join/Split |
| 40 | `splitlines(keepends=False)` | Split string at line boundaries, return list of lines | Join/Split |
| 41 | `startswith(prefix, start, end)` | Return True if string starts with the given prefix | Test |
| 42 | `strip(chars=None)` | Return string with leading and trailing characters removed | Strip |
| 43 | `swapcase()` | Return string with uppercase chars lowered and vice versa | Case |
| 44 | `title()` | Return titlecased version of the string | Case |
| 45 | `translate(table)` | Replace characters using the given translation table | Transform |
| 46 | `upper()` | Return uppercased copy of the string | Case |
| 47 | `zfill(width)` | Pad string on the left with zeros to fill given width | Alignment |

### 1.2 string Module Functions

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `string.ascii_letters` | Concatenation of ascii_lowercase and ascii_uppercase | Constant |
| 2 | `string.ascii_lowercase` | The lowercase letters 'abcdefghijklmnopqrstuvwxyz' | Constant |
| 3 | `string.ascii_uppercase` | The uppercase letters 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' | Constant |
| 4 | `string.digits` | The string '0123456789' | Constant |
| 5 | `string.hexdigits` | The string '0123456789abcdefABCDEF' | Constant |
| 6 | `string.octdigits` | The string '01234567' | Constant |
| 7 | `string.printable` | All printable ASCII characters | Constant |
| 8 | `string.punctuation` | All ASCII punctuation characters | Constant |
| 9 | `string.whitespace` | All ASCII whitespace characters | Constant |
| 10 | `string.capwords(s, sep=None)` | Split, capitalize each word, rejoin | Function |
| 11 | `string.Template(template)` | Simple $-based string substitution class | Class |
| 12 | `string.Formatter()` | Custom string formatting class | Class |

### 1.3 textwrap Module

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `textwrap.wrap(text, width=70)` | Wrap text into a list of lines at given width | Wrapping |
| 2 | `textwrap.fill(text, width=70)` | Wrap text and return single string with newlines | Wrapping |
| 3 | `textwrap.shorten(text, width)` | Truncate text to fit in given width with placeholder | Wrapping |
| 4 | `textwrap.dedent(text)` | Remove common leading whitespace from all lines | Indentation |
| 5 | `textwrap.indent(text, prefix)` | Add prefix to the beginning of selected lines | Indentation |
| 6 | `textwrap.TextWrapper(**kwargs)` | Class for fine-grained control over text wrapping | Class |

### 1.4 re Module (Regular Expressions)

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `re.compile(pattern, flags=0)` | Compile regex pattern into a reusable pattern object | Compilation |
| 2 | `re.search(pattern, string, flags=0)` | Search for first match anywhere in the string | Matching |
| 3 | `re.match(pattern, string, flags=0)` | Match pattern only at the beginning of the string | Matching |
| 4 | `re.fullmatch(pattern, string, flags=0)` | Match pattern against the entire string | Matching |
| 5 | `re.findall(pattern, string, flags=0)` | Return list of all non-overlapping matches | Search |
| 6 | `re.finditer(pattern, string, flags=0)` | Return iterator of match objects for all matches | Search |
| 7 | `re.sub(pattern, repl, string, count=0)` | Replace occurrences of pattern with replacement | Replace |
| 8 | `re.subn(pattern, repl, string, count=0)` | Like sub() but also returns count of replacements | Replace |
| 9 | `re.split(pattern, string, maxsplit=0)` | Split string by occurrences of pattern | Split |
| 10 | `re.escape(pattern)` | Escape all non-alphanumeric characters in pattern | Utility |
| 11 | `re.purge()` | Clear the regular expression cache | Utility |

**Match Object Methods:**

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `match.group(num=0)` | Return matched string or specific group | Access |
| 2 | `match.groups(default=None)` | Return tuple of all matched groups | Access |
| 3 | `match.groupdict(default=None)` | Return dict of named groups | Access |
| 4 | `match.start(group=0)` | Return start position of the match | Position |
| 5 | `match.end(group=0)` | Return end position of the match | Position |
| 6 | `match.span(group=0)` | Return tuple (start, end) of the match | Position |
| 7 | `match.expand(template)` | Return string from template with backslash substitutions | Transform |
| 8 | `match.lastgroup` | Name of the last matched group | Attribute |
| 9 | `match.lastindex` | Index of the last matched group | Attribute |
| 10 | `match.re` | The regex pattern object used | Attribute |
| 11 | `match.string` | The string passed to match/search | Attribute |

**re Flags:**

| # | Flag | Description | Category |
|---|------|-------------|----------|
| 1 | `re.IGNORECASE` / `re.I` | Case-insensitive matching | Flag |
| 2 | `re.MULTILINE` / `re.M` | ^ and $ match at line boundaries | Flag |
| 3 | `re.DOTALL` / `re.S` | Dot matches newline characters | Flag |
| 4 | `re.VERBOSE` / `re.X` | Allow comments and whitespace in pattern | Flag |
| 5 | `re.ASCII` / `re.A` | Make \w, \b, \d, \s match ASCII only | Flag |
| 6 | `re.UNICODE` / `re.U` | Make \w, \b, \d, \s match Unicode (default) | Flag |

---

## 2. File/Path Methods

### 2.1 Built-in open() and File Object Methods

| # | Function/Method | Description | Category |
|---|-----------------|-------------|----------|
| 1 | `open(file, mode='r', buffering=-1, encoding=None, errors=None, newline=None, closefd=True, opener=None)` | Open file and return a file object | Open |
| 2 | `file.read(size=-1)` | Read and return up to size bytes/characters (-1 = all) | Read |
| 3 | `file.readline(size=-1)` | Read and return one line from the file | Read |
| 4 | `file.readlines(hint=-1)` | Read and return list of lines from the file | Read |
| 5 | `file.write(s)` | Write string/bytes to file, return number of characters written | Write |
| 6 | `file.writelines(lines)` | Write a list of lines to the file (no newlines added) | Write |
| 7 | `file.seek(offset, whence=0)` | Move file position to given offset (0=start, 1=current, 2=end) | Navigation |
| 8 | `file.tell()` | Return current file position as integer | Navigation |
| 9 | `file.close()` | Flush and close the file object | Lifecycle |
| 10 | `file.flush()` | Flush the write buffer to the file | Lifecycle |
| 11 | `file.truncate(size=None)` | Truncate file to at most size bytes | Modify |
| 12 | `file.fileno()` | Return the underlying file descriptor integer | Info |
| 13 | `file.isatty()` | Return True if file is connected to a terminal device | Info |
| 14 | `file.readable()` | Return True if the file can be read | Info |
| 15 | `file.writable()` | Return True if the file can be written to | Info |
| 16 | `file.seekable()` | Return True if the file supports random access | Info |
| 17 | `file.closed` | True if the file has been closed | Attribute |
| 18 | `file.name` | Name of the file | Attribute |
| 19 | `file.mode` | Mode the file was opened in | Attribute |
| 20 | `file.encoding` | Encoding used for text mode files | Attribute |

**File open() modes:**

| Mode | Description |
|------|-------------|
| `'r'` | Read text (default) |
| `'w'` | Write text (truncates) |
| `'a'` | Append text |
| `'x'` | Exclusive create (fails if exists) |
| `'b'` | Binary mode (combine: `'rb'`, `'wb'`) |
| `'t'` | Text mode (default, combine: `'rt'`) |
| `'+'` | Read and write (combine: `'r+'`, `'w+'`) |

### 2.2 pathlib.Path Methods and Properties

| # | Method/Property | Description | Category |
|---|-----------------|-------------|----------|
| 1 | `Path(path_string)` | Create a new Path object | Constructor |
| 2 | `Path.cwd()` | Return Path of current working directory | Constructor |
| 3 | `Path.home()` | Return Path of user's home directory | Constructor |
| 4 | `path.exists()` | Return True if path exists on filesystem | Test |
| 5 | `path.is_file()` | Return True if path is a regular file | Test |
| 6 | `path.is_dir()` | Return True if path is a directory | Test |
| 7 | `path.is_symlink()` | Return True if path is a symbolic link | Test |
| 8 | `path.is_mount()` | Return True if path is a mount point | Test |
| 9 | `path.is_socket()` | Return True if path is a Unix socket | Test |
| 10 | `path.is_fifo()` | Return True if path is a FIFO (named pipe) | Test |
| 11 | `path.is_block_device()` | Return True if path is a block device | Test |
| 12 | `path.is_char_device()` | Return True if path is a character device | Test |
| 13 | `path.is_absolute()` | Return True if path is absolute | Test |
| 14 | `path.is_relative_to(other)` | Return True if path is relative to other (3.9+) | Test |
| 15 | `path.mkdir(mode=0o777, parents=False, exist_ok=False)` | Create directory at this path | Filesystem |
| 16 | `path.rmdir()` | Remove empty directory at this path | Filesystem |
| 17 | `path.rename(target)` | Rename this path to target, return new Path | Filesystem |
| 18 | `path.replace(target)` | Rename, unconditionally replacing target | Filesystem |
| 19 | `path.unlink(missing_ok=False)` | Remove this file or symbolic link | Filesystem |
| 20 | `path.symlink_to(target)` | Make this path a symbolic link to target | Filesystem |
| 21 | `path.hardlink_to(target)` | Make this path a hard link to target (3.10+) | Filesystem |
| 22 | `path.touch(mode=0o666, exist_ok=True)` | Create file or update modification time | Filesystem |
| 23 | `path.chmod(mode)` | Change file mode and permissions | Filesystem |
| 24 | `path.lchmod(mode)` | Like chmod but on the symlink itself | Filesystem |
| 25 | `path.stat()` | Return os.stat_result for the path | Info |
| 26 | `path.lstat()` | Like stat but on the symlink itself | Info |
| 27 | `path.owner()` | Return name of the file owner | Info |
| 28 | `path.group()` | Return name of the file group | Info |
| 29 | `path.glob(pattern)` | Glob the given pattern in this directory, yield matches | Search |
| 30 | `path.rglob(pattern)` | Recursive glob, equivalent to `**/pattern` | Search |
| 31 | `path.iterdir()` | Yield Path objects of directory contents | Search |
| 32 | `path.walk(top_down=True)` | Walk directory tree recursively (3.12+) | Search |
| 33 | `path.resolve(strict=False)` | Make path absolute, resolving all symlinks | Transform |
| 34 | `path.absolute()` | Make path absolute without resolving symlinks | Transform |
| 35 | `path.expanduser()` | Expand ~ and ~user constructs | Transform |
| 36 | `path.relative_to(other)` | Return relative path from other to self | Transform |
| 37 | `path.with_name(name)` | Return new path with the name changed | Transform |
| 38 | `path.with_stem(stem)` | Return new path with the stem changed (3.9+) | Transform |
| 39 | `path.with_suffix(suffix)` | Return new path with the suffix changed | Transform |
| 40 | `path.with_segments(*args)` | Return new path with segments replaced (3.12+) | Transform |
| 41 | `path.joinpath(*args)` | Combine path with additional parts | Transform |
| 42 | `path.match(pattern)` | Match path against a glob-style pattern | Test |
| 43 | `path.read_text(encoding=None, errors=None)` | Read file contents as string | I/O |
| 44 | `path.read_bytes()` | Read file contents as bytes | I/O |
| 45 | `path.write_text(data, encoding=None, errors=None)` | Write string data to file | I/O |
| 46 | `path.write_bytes(data)` | Write bytes data to file | I/O |
| 47 | `path.open(mode='r', buffering=-1, encoding=None)` | Open file at path (like built-in open) | I/O |
| 48 | `path.name` | Final component of the path (e.g., 'file.txt') | Property |
| 49 | `path.stem` | Final component without suffix (e.g., 'file') | Property |
| 50 | `path.suffix` | File extension including dot (e.g., '.txt') | Property |
| 51 | `path.suffixes` | List of all file extensions (e.g., ['.tar', '.gz']) | Property |
| 52 | `path.parent` | Logical parent of the path | Property |
| 53 | `path.parents` | Immutable sequence of all logical parent paths | Property |
| 54 | `path.parts` | Tuple of path components (e.g., ('/', 'usr', 'bin')) | Property |
| 55 | `path.root` | String representing the root (e.g., '/') | Property |
| 56 | `path.anchor` | Concatenation of drive and root | Property |
| 57 | `path.drive` | Drive letter on Windows (empty on POSIX) | Property |
| 58 | `path.as_posix()` | Return string with forward slashes | Convert |
| 59 | `path.as_uri()` | Return path as file:// URI | Convert |

### 2.3 os.path Functions

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `os.path.join(path, *paths)` | Join path components intelligently | Build |
| 2 | `os.path.split(path)` | Split path into (directory, filename) tuple | Split |
| 3 | `os.path.splitext(path)` | Split path into (root, extension) tuple | Split |
| 4 | `os.path.splitdrive(path)` | Split path into (drive, tail) tuple | Split |
| 5 | `os.path.basename(path)` | Return final component of the path | Extract |
| 6 | `os.path.dirname(path)` | Return directory component of the path | Extract |
| 7 | `os.path.exists(path)` | Return True if path exists | Test |
| 8 | `os.path.lexists(path)` | Return True if path exists (follows no symlinks) | Test |
| 9 | `os.path.isfile(path)` | Return True if path is a regular file | Test |
| 10 | `os.path.isdir(path)` | Return True if path is a directory | Test |
| 11 | `os.path.islink(path)` | Return True if path is a symbolic link | Test |
| 12 | `os.path.ismount(path)` | Return True if path is a mount point | Test |
| 13 | `os.path.isabs(path)` | Return True if path is absolute | Test |
| 14 | `os.path.getsize(path)` | Return size in bytes of the file | Info |
| 15 | `os.path.getmtime(path)` | Return last modification time | Info |
| 16 | `os.path.getctime(path)` | Return creation time (or metadata change on Unix) | Info |
| 17 | `os.path.getatime(path)` | Return last access time | Info |
| 18 | `os.path.abspath(path)` | Return absolute version of the path | Transform |
| 19 | `os.path.realpath(path)` | Return canonical path resolving symlinks | Transform |
| 20 | `os.path.relpath(path, start=os.curdir)` | Return relative path from start to path | Transform |
| 21 | `os.path.expanduser(path)` | Expand ~ and ~user in path | Transform |
| 22 | `os.path.expandvars(path)` | Expand environment variables in path | Transform |
| 23 | `os.path.normpath(path)` | Normalize path (remove redundant separators, up-levels) | Transform |
| 24 | `os.path.normcase(path)` | Normalize case (lowercase on Windows, identity on POSIX) | Transform |
| 25 | `os.path.commonpath(paths)` | Return longest common sub-path of each path | Compare |
| 26 | `os.path.commonprefix(list)` | Return longest common prefix of all paths (char-based) | Compare |
| 27 | `os.path.samefile(path1, path2)` | Return True if both paths refer to the same file | Compare |
| 28 | `os.path.sameopenfile(fp1, fp2)` | Return True if file descriptors refer to same file | Compare |
| 29 | `os.path.samestat(stat1, stat2)` | Return True if stat results refer to same file | Compare |

### 2.4 shutil Module

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `shutil.copy(src, dst)` | Copy file (content + permissions) to dst | Copy |
| 2 | `shutil.copy2(src, dst)` | Copy file (content + metadata) to dst | Copy |
| 3 | `shutil.copyfile(src, dst)` | Copy file content only (no metadata) | Copy |
| 4 | `shutil.copyfileobj(fsrc, fdst, length=16384)` | Copy file object contents | Copy |
| 5 | `shutil.copymode(src, dst)` | Copy permission bits from src to dst | Copy |
| 6 | `shutil.copystat(src, dst)` | Copy permission bits, timestamps, flags | Copy |
| 7 | `shutil.copytree(src, dst, dirs_exist_ok=False)` | Recursively copy entire directory tree | Copy |
| 8 | `shutil.rmtree(path, ignore_errors=False)` | Recursively delete a directory tree | Delete |
| 9 | `shutil.move(src, dst)` | Recursively move file or directory to dst | Move |
| 10 | `shutil.disk_usage(path)` | Return disk usage statistics (total, used, free) | Info |
| 11 | `shutil.which(name, mode=os.F_OK|os.X_OK)` | Find executable in PATH (like Unix which) | Search |
| 12 | `shutil.chown(path, user=None, group=None)` | Change owner/group of a file | Permissions |
| 13 | `shutil.make_archive(base_name, format, root_dir)` | Create an archive file (zip, tar, etc.) | Archive |
| 14 | `shutil.unpack_archive(filename, extract_dir)` | Unpack an archive file | Archive |
| 15 | `shutil.get_archive_formats()` | Return list of supported archive formats | Archive |
| 16 | `shutil.get_unpack_formats()` | Return list of supported unpack formats | Archive |
| 17 | `shutil.get_terminal_size(fallback=(80, 24))` | Get terminal window size | Info |

---

## 3. Collection Methods

### 3.1 List Methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `list.append(x)` | Add item to the end of the list | Add |
| 2 | `list.extend(iterable)` | Extend list by appending all items from iterable | Add |
| 3 | `list.insert(i, x)` | Insert item at given position | Add |
| 4 | `list.remove(x)` | Remove first occurrence of value (raises ValueError) | Remove |
| 5 | `list.pop(i=-1)` | Remove and return item at index (default last) | Remove |
| 6 | `list.clear()` | Remove all items from the list | Remove |
| 7 | `list.index(x, start=0, end=len)` | Return index of first occurrence of value | Search |
| 8 | `list.count(x)` | Return number of occurrences of value | Search |
| 9 | `list.sort(key=None, reverse=False)` | Sort list in place | Order |
| 10 | `list.reverse()` | Reverse list in place | Order |
| 11 | `list.copy()` | Return a shallow copy of the list | Copy |

### 3.2 Dict Methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `dict.keys()` | Return view of dictionary keys | View |
| 2 | `dict.values()` | Return view of dictionary values | View |
| 3 | `dict.items()` | Return view of (key, value) pairs | View |
| 4 | `dict.get(key, default=None)` | Return value for key, or default if missing | Access |
| 5 | `dict.setdefault(key, default=None)` | Return value for key; if missing, insert default and return it | Access |
| 6 | `dict.update(other)` | Update dict with key/value pairs from other dict/iterable | Modify |
| 7 | `dict.pop(key, default)` | Remove and return value for key (or default) | Remove |
| 8 | `dict.popitem()` | Remove and return last inserted (key, value) pair | Remove |
| 9 | `dict.clear()` | Remove all items from the dictionary | Remove |
| 10 | `dict.copy()` | Return a shallow copy of the dictionary | Copy |
| 11 | `dict.fromkeys(iterable, value=None)` | Create new dict with keys from iterable, all set to value | Constructor |
| 12 | `dict.__or__(other)` | Merge dicts: `d1 | d2` (3.9+) | Merge |
| 13 | `dict.__ior__(other)` | Update-merge: `d1 |= d2` (3.9+) | Merge |

### 3.3 Set Methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `set.add(elem)` | Add element to the set | Add |
| 2 | `set.remove(elem)` | Remove element (raises KeyError if absent) | Remove |
| 3 | `set.discard(elem)` | Remove element if present (no error if absent) | Remove |
| 4 | `set.pop()` | Remove and return an arbitrary element | Remove |
| 5 | `set.clear()` | Remove all elements from the set | Remove |
| 6 | `set.copy()` | Return a shallow copy of the set | Copy |
| 7 | `set.union(*others)` | Return set with elements from self and all others | Set Ops |
| 8 | `set.intersection(*others)` | Return set with elements common to self and all others | Set Ops |
| 9 | `set.difference(*others)` | Return set with elements in self but not in others | Set Ops |
| 10 | `set.symmetric_difference(other)` | Return set with elements in either but not both | Set Ops |
| 11 | `set.issubset(other)` | Return True if every element is in other | Test |
| 12 | `set.issuperset(other)` | Return True if every element of other is in self | Test |
| 13 | `set.isdisjoint(other)` | Return True if sets have no elements in common | Test |
| 14 | `set.update(*others)` | Add all elements from others to self | Modify |
| 15 | `set.intersection_update(*others)` | Keep only elements found in self and all others | Modify |
| 16 | `set.difference_update(*others)` | Remove all elements found in others | Modify |
| 17 | `set.symmetric_difference_update(other)` | Keep elements in either but not both | Modify |

### 3.4 Tuple Methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `tuple.count(x)` | Return number of occurrences of value | Search |
| 2 | `tuple.index(x, start=0, end=len)` | Return index of first occurrence of value | Search |

### 3.5 collections Module

| # | Class/Function | Description | Category |
|---|----------------|-------------|----------|
| 1 | `Counter(iterable_or_mapping)` | Dict subclass for counting hashable objects | Counting |
| 2 | `Counter.most_common(n=None)` | Return n most common elements and counts | Counting |
| 3 | `Counter.elements()` | Return iterator over elements repeating by count | Counting |
| 4 | `Counter.subtract(iterable_or_mapping)` | Subtract counts element-wise | Counting |
| 5 | `Counter.total()` | Sum of all counts (3.10+) | Counting |
| 6 | `Counter.update(iterable_or_mapping)` | Add counts from iterable or mapping | Counting |
| 7 | `defaultdict(default_factory)` | Dict subclass with default value factory for missing keys | Dict |
| 8 | `OrderedDict()` | Dict subclass that remembers insertion order | Dict |
| 9 | `OrderedDict.move_to_end(key, last=True)` | Move existing key to either end | Dict |
| 10 | `OrderedDict.popitem(last=True)` | Remove and return (key, value) from either end | Dict |
| 11 | `deque(iterable=(), maxlen=None)` | Double-ended queue with O(1) append/pop on both ends | Sequence |
| 12 | `deque.append(x)` | Add element to the right side | Sequence |
| 13 | `deque.appendleft(x)` | Add element to the left side | Sequence |
| 14 | `deque.extend(iterable)` | Extend right side with elements from iterable | Sequence |
| 15 | `deque.extendleft(iterable)` | Extend left side with elements from iterable | Sequence |
| 16 | `deque.pop()` | Remove and return element from right side | Sequence |
| 17 | `deque.popleft()` | Remove and return element from left side | Sequence |
| 18 | `deque.rotate(n=1)` | Rotate deque n steps to the right | Sequence |
| 19 | `deque.clear()` | Remove all elements from the deque | Sequence |
| 20 | `deque.copy()` | Return a shallow copy of the deque | Sequence |
| 21 | `deque.count(x)` | Count number of occurrences of x | Sequence |
| 22 | `deque.index(x, start=0, stop=len)` | Return index of first occurrence of x | Sequence |
| 23 | `deque.insert(i, x)` | Insert x at position i | Sequence |
| 24 | `deque.remove(x)` | Remove first occurrence of x | Sequence |
| 25 | `deque.reverse()` | Reverse deque in place | Sequence |
| 26 | `deque.maxlen` | Maximum size of the deque (None if unbounded) | Attribute |
| 27 | `namedtuple(typename, field_names)` | Factory for tuple subclasses with named fields | Tuple |
| 28 | `namedtuple._make(iterable)` | Class method to create instance from iterable | Tuple |
| 29 | `namedtuple._asdict()` | Return OrderedDict of field name to value | Tuple |
| 30 | `namedtuple._replace(**kwargs)` | Return new instance with specified fields replaced | Tuple |
| 31 | `namedtuple._fields` | Tuple of field names | Tuple |
| 32 | `namedtuple._field_defaults` | Dict of fields with default values | Tuple |
| 33 | `ChainMap(*maps)` | Group multiple dicts into a single searchable view | Dict |
| 34 | `ChainMap.maps` | List of mappings ordered first-to-last searched | Dict |
| 35 | `ChainMap.new_child(m=None)` | Return new ChainMap with new map followed by existing | Dict |
| 36 | `ChainMap.parents` | Property returning new ChainMap without first map | Dict |
| 37 | `UserDict(initialdata)` | Wrapper around dict for easier subclassing | Wrapper |
| 38 | `UserList(initialdata)` | Wrapper around list for easier subclassing | Wrapper |
| 39 | `UserString(seq)` | Wrapper around string for easier subclassing | Wrapper |

### 3.6 itertools Module

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `chain(*iterables)` | Chain multiple iterables into a single sequence | Combine |
| 2 | `chain.from_iterable(iterable)` | Alternate constructor chaining from a single iterable of iterables | Combine |
| 3 | `combinations(iterable, r)` | Return r-length subsequences of elements (no repeats) | Combinatoric |
| 4 | `combinations_with_replacement(iterable, r)` | Return r-length subsequences allowing repeated elements | Combinatoric |
| 5 | `permutations(iterable, r=None)` | Return r-length permutations of elements | Combinatoric |
| 6 | `product(*iterables, repeat=1)` | Return Cartesian product of input iterables | Combinatoric |
| 7 | `repeat(object, times=None)` | Return object repeatedly (times or infinitely) | Infinite |
| 8 | `count(start=0, step=1)` | Return evenly spaced values starting from start | Infinite |
| 9 | `cycle(iterable)` | Return elements cycling endlessly over the iterable | Infinite |
| 10 | `zip_longest(*iterables, fillvalue=None)` | Zip iterables padding shorter ones with fillvalue | Combine |
| 11 | `groupby(iterable, key=None)` | Group consecutive elements by key function | Group |
| 12 | `islice(iterable, stop)` / `islice(iterable, start, stop, step)` | Slice an iterator like list slicing | Slice |
| 13 | `takewhile(predicate, iterable)` | Yield elements while predicate is True | Filter |
| 14 | `dropwhile(predicate, iterable)` | Skip elements while predicate is True, then yield rest | Filter |
| 15 | `filterfalse(predicate, iterable)` | Yield elements where predicate is False | Filter |
| 16 | `compress(data, selectors)` | Filter data using corresponding boolean selectors | Filter |
| 17 | `starmap(function, iterable)` | Apply function with argument tuples from iterable | Map |
| 18 | `accumulate(iterable, func=operator.add, initial=None)` | Return running totals (or accumulated results) | Reduce |
| 19 | `tee(iterable, n=2)` | Return n independent iterators from a single iterable | Split |
| 20 | `pairwise(iterable)` | Return consecutive overlapping pairs (3.10+) | Combine |
| 21 | `batched(iterable, n)` | Batch data into tuples of length n (3.12+) | Group |

### 3.7 functools Module

| # | Function/Decorator | Description | Category |
|---|-------------------|-------------|----------|
| 1 | `reduce(function, iterable, initializer=None)` | Apply function cumulatively to reduce iterable to single value | Reduce |
| 2 | `partial(func, *args, **kwargs)` | Return new function with some arguments pre-filled | Partial |
| 3 | `partialmethod(func, *args, **kwargs)` | Like partial but for use as a method descriptor | Partial |
| 4 | `lru_cache(maxsize=128, typed=False)` | Decorator to cache function results (LRU eviction) | Cache |
| 5 | `cache(func)` | Simple unbounded cache decorator (3.9+, equivalent to lru_cache(maxsize=None)) | Cache |
| 6 | `cached_property(func)` | Decorator to cache a property value on first access | Cache |
| 7 | `wraps(wrapped)` | Decorator to copy metadata from wrapped function | Decorator |
| 8 | `total_ordering` | Class decorator to fill in missing comparison methods | Ordering |
| 9 | `cmp_to_key(func)` | Convert old-style comparison function to a key function | Ordering |
| 10 | `singledispatch(func)` | Decorator for single-dispatch generic functions | Dispatch |
| 11 | `singledispatchmethod(func)` | Like singledispatch but for class methods | Dispatch |
| 12 | `update_wrapper(wrapper, wrapped)` | Update wrapper function to look like wrapped function | Decorator |

### 3.8 Built-in Functions for Collections

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `map(function, iterable, *iterables)` | Apply function to every item, return iterator | Transform |
| 2 | `filter(function, iterable)` | Return iterator of items where function returns True | Filter |
| 3 | `zip(*iterables, strict=False)` | Aggregate elements from each iterable into tuples | Combine |
| 4 | `enumerate(iterable, start=0)` | Return iterator of (index, value) pairs | Index |
| 5 | `sorted(iterable, key=None, reverse=False)` | Return new sorted list from iterable | Order |
| 6 | `reversed(sequence)` | Return a reverse iterator over the sequence | Order |
| 7 | `any(iterable)` | Return True if any element is truthy | Test |
| 8 | `all(iterable)` | Return True if all elements are truthy | Test |
| 9 | `min(iterable, key=None, default=...)` | Return smallest element | Aggregate |
| 10 | `max(iterable, key=None, default=...)` | Return largest element | Aggregate |
| 11 | `sum(iterable, start=0)` | Return sum of all elements plus start | Aggregate |
| 12 | `len(s)` | Return number of items in a container | Aggregate |
| 13 | `list(iterable)` | Create list from iterable | Constructor |
| 14 | `tuple(iterable)` | Create tuple from iterable | Constructor |
| 15 | `dict(**kwargs)` / `dict(mapping)` | Create dictionary | Constructor |
| 16 | `set(iterable)` | Create set from iterable | Constructor |
| 17 | `frozenset(iterable)` | Create immutable set from iterable | Constructor |
| 18 | `range(stop)` / `range(start, stop, step)` | Return immutable sequence of numbers | Constructor |
| 19 | `iter(object)` / `iter(callable, sentinel)` | Return an iterator object | Iterator |
| 20 | `next(iterator, default=...)` | Retrieve next item from iterator | Iterator |
| 21 | `abs(x)` | Return absolute value | Math |
| 22 | `round(number, ndigits=None)` | Round number to given precision | Math |
| 23 | `pow(base, exp, mod=None)` | Return base to the power exp (optionally mod) | Math |
| 24 | `divmod(a, b)` | Return (quotient, remainder) pair | Math |
| 25 | `hash(object)` | Return hash value of the object | Hash |
| 26 | `id(object)` | Return unique identity of the object | Identity |
| 27 | `type(object)` | Return type of the object | Type |
| 28 | `isinstance(object, classinfo)` | Return True if object is instance of classinfo | Type |
| 29 | `issubclass(class, classinfo)` | Return True if class is subclass of classinfo | Type |
| 30 | `callable(object)` | Return True if object appears callable | Type |
| 31 | `getattr(object, name, default=...)` | Return attribute value of object | Attribute |
| 32 | `setattr(object, name, value)` | Set attribute value on object | Attribute |
| 33 | `delattr(object, name)` | Delete attribute from object | Attribute |
| 34 | `hasattr(object, name)` | Return True if object has the named attribute | Attribute |
| 35 | `repr(object)` | Return printable representation string | String |
| 36 | `str(object)` | Return string version of object | String |
| 37 | `format(value, format_spec='')` | Format value according to format_spec | String |
| 38 | `print(*objects, sep=' ', end='\n', file=sys.stdout)` | Print objects to text stream | I/O |
| 39 | `input(prompt='')` | Read line from input | I/O |
| 40 | `int(x=0, base=10)` | Convert to integer | Convert |
| 41 | `float(x=0)` | Convert to float | Convert |
| 42 | `complex(real=0, imag=0)` | Create complex number | Convert |
| 43 | `bool(x=False)` | Convert to boolean | Convert |
| 44 | `bytes(source, encoding, errors)` | Create bytes object | Convert |
| 45 | `bytearray(source, encoding, errors)` | Create mutable bytes object | Convert |
| 46 | `memoryview(obj)` | Create memory view of bytes-like object | Convert |
| 47 | `bin(x)` | Convert integer to binary string | Convert |
| 48 | `oct(x)` | Convert integer to octal string | Convert |
| 49 | `hex(x)` | Convert integer to hexadecimal string | Convert |
| 50 | `ord(c)` | Return Unicode code point for one-character string | Convert |
| 51 | `chr(i)` | Return string for a Unicode code point | Convert |
| 52 | `ascii(object)` | Return ASCII-only repr with non-ASCII chars escaped | Convert |
| 53 | `vars(object)` | Return __dict__ of object | Introspection |
| 54 | `dir(object)` | Return list of names in scope or object's attributes | Introspection |
| 55 | `globals()` | Return dict of global symbol table | Introspection |
| 56 | `locals()` | Return dict of local symbol table | Introspection |
| 57 | `help(object)` | Invoke built-in help system | Introspection |
| 58 | `property(fget, fset, fdel, doc)` | Return a property attribute | Descriptor |
| 59 | `staticmethod(function)` | Convert method to static method | Descriptor |
| 60 | `classmethod(function)` | Convert method to class method | Descriptor |
| 61 | `super(type, object_or_type)` | Return proxy for parent class delegation | OOP |
| 62 | `object()` | Return featureless base object | OOP |
| 63 | `__import__(name)` | Invoked by import statement | Import |
| 64 | `compile(source, filename, mode)` | Compile source into code object | Code |
| 65 | `eval(expression, globals, locals)` | Evaluate expression string | Code |
| 66 | `exec(code, globals, locals)` | Execute code string or code object | Code |
| 67 | `breakpoint(*args, **kws)` | Drop into debugger (3.7+) | Debug |
| 68 | `open(file, mode='r', ...)` | Open file and return file object | I/O |
| 69 | `slice(stop)` / `slice(start, stop, step)` | Return a slice object | Sequence |
| 70 | `aiter(async_iterable)` | Return async iterator (3.10+) | Async |
| 71 | `anext(async_iterator, default=...)` | Retrieve next item from async iterator (3.10+) | Async |

---

## Summary Statistics

| Category | Count |
|----------|-------|
| str methods | 47 |
| string module | 12 |
| textwrap module | 6 |
| re module (functions + match + flags) | 28 |
| File open/object | 20 |
| pathlib.Path | 59 |
| os.path | 29 |
| shutil | 17 |
| list methods | 11 |
| dict methods | 13 |
| set methods | 17 |
| tuple methods | 2 |
| collections module | 39 |
| itertools module | 21 |
| functools module | 12 |
| Built-in functions | 71 |
| **TOTAL** | **404** |
