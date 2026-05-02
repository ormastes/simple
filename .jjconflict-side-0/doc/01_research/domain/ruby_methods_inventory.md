# Ruby Methods Comprehensive Inventory

Complete reference of all helper methods for String, File/IO, and Collection classes.

---

## 1. String Methods

### Operators & Comparison

| Method | Description | Category |
|--------|-------------|----------|
| `+` | Concatenates two strings, returns new string | Operator |
| `*` | Repeats string n times, returns new string | Operator |
| `<<` | Appends string in-place (mutates receiver) | Operator |
| `<=>` | Spaceship comparison, returns -1/0/1/nil | Comparison |
| `==` | Equality check, returns true/false | Comparison |
| `=~` | Pattern match against regexp, returns index or nil | Pattern |
| `[]` | Slice/reference by index, range, regexp, or string | Access |
| `[]=` | Replace substring by index, range, regexp, or string | Access |
| `eql?` | Strict equality (same content and encoding) | Comparison |
| `hash` | Returns hash value for use in Hash keys | Comparison |

### Encoding & Bytes

| Method | Description | Category |
|--------|-------------|----------|
| `ascii_only?` | Returns true if string contains only ASCII characters | Encoding |
| `b` | Returns a copy of string with ASCII-8BIT encoding | Encoding |
| `bytes` | Returns array of bytes (integers) | Encoding |
| `bytesize` | Returns length in bytes (not characters) | Encoding |
| `byteslice` | Returns substring by byte offset and length | Encoding |
| `encode` | Returns string transcoded to specified encoding | Encoding |
| `encoding` | Returns the Encoding object for the string | Encoding |
| `force_encoding` | Changes encoding tag without transcoding bytes | Encoding |
| `getbyte` | Returns byte at given index as integer | Encoding |
| `ord` | Returns integer ordinal of first character | Encoding |
| `scrub` | Returns copy with invalid byte sequences replaced | Encoding |
| `scrub!` | Replaces invalid byte sequences in place | Encoding |
| `setbyte` | Sets byte at given index | Encoding |
| `unicode_normalize` | Returns Unicode-normalized copy (NFC/NFD/NFKC/NFKD) | Encoding |
| `unicode_normalize!` | Unicode-normalizes in place | Encoding |
| `valid_encoding?` | Returns true if string has valid encoding | Encoding |

### Case Conversion

| Method | Description | Category |
|--------|-------------|----------|
| `capitalize` | Returns copy with first char uppercased, rest lowercased | Case |
| `capitalize!` | Capitalizes in place, returns nil if no change | Case |
| `casecmp` | Case-insensitive <=> comparison, returns -1/0/1/nil | Case |
| `casecmp?` | Case-insensitive equality, returns true/false/nil | Case |
| `downcase` | Returns copy with all chars lowercased | Case |
| `downcase!` | Lowercases in place, returns nil if no change | Case |
| `swapcase` | Returns copy with upper/lower swapped | Case |
| `swapcase!` | Swaps case in place, returns nil if no change | Case |
| `upcase` | Returns copy with all chars uppercased | Case |
| `upcase!` | Uppercases in place, returns nil if no change | Case |

### Searching & Matching

| Method | Description | Category |
|--------|-------------|----------|
| `count` | Counts occurrences of characters in intersection of sets | Search |
| `empty?` | Returns true if string has zero length | Search |
| `end_with?` | Returns true if string ends with any given suffix | Search |
| `include?` | Returns true if string contains given substring | Search |
| `index` | Returns first index of substring/regexp, or nil | Search |
| `match` | Matches against regexp, returns MatchData or nil | Search |
| `match?` | Returns true/false for regexp match (no MatchData) | Search |
| `rindex` | Returns last index of substring/regexp, or nil | Search |
| `scan` | Returns array of all matches of pattern | Search |
| `start_with?` | Returns true if string starts with any given prefix | Search |

### Substitution & Transformation

| Method | Description | Category |
|--------|-------------|----------|
| `center` | Centers string in width with optional pad character | Format |
| `chomp` | Returns copy with trailing record separator removed | Strip |
| `chomp!` | Removes trailing record separator in place | Strip |
| `chop` | Returns copy with last character removed | Strip |
| `chop!` | Removes last character in place | Strip |
| `chr` | Returns first character of string | Access |
| `clear` | Removes all content, making string empty | Mutate |
| `concat` | Appends strings/codepoints to self (alias of <<) | Mutate |
| `delete` | Returns copy with all characters in intersection removed | Transform |
| `delete!` | Deletes characters in place | Transform |
| `delete_prefix` | Returns copy with leading prefix removed if present | Transform |
| `delete_prefix!` | Removes leading prefix in place | Transform |
| `delete_suffix` | Returns copy with trailing suffix removed if present | Transform |
| `delete_suffix!` | Removes trailing suffix in place | Transform |
| `gsub` | Returns copy with all pattern matches replaced | Transform |
| `gsub!` | Replaces all pattern matches in place | Transform |
| `insert` | Inserts string at given index position | Mutate |
| `ljust` | Left-justifies string in width with optional pad | Format |
| `lstrip` | Returns copy with leading whitespace removed | Strip |
| `lstrip!` | Removes leading whitespace in place | Strip |
| `next` | Returns next string in sequence (alias of succ) | Transform |
| `next!` | Increments string in place (alias of succ!) | Transform |
| `prepend` | Prepends strings to the beginning of self | Mutate |
| `replace` | Replaces entire contents with another string | Mutate |
| `reverse` | Returns copy with characters in reverse order | Transform |
| `reverse!` | Reverses characters in place | Transform |
| `rjust` | Right-justifies string in width with optional pad | Format |
| `rstrip` | Returns copy with trailing whitespace removed | Strip |
| `rstrip!` | Removes trailing whitespace in place | Strip |
| `squeeze` | Returns copy with runs of same char reduced to one | Transform |
| `squeeze!` | Squeezes runs of same char in place | Transform |
| `strip` | Returns copy with leading and trailing whitespace removed | Strip |
| `strip!` | Strips leading and trailing whitespace in place | Strip |
| `sub` | Returns copy with first pattern match replaced | Transform |
| `sub!` | Replaces first pattern match in place | Transform |
| `succ` | Returns next string in alphabetical sequence | Transform |
| `succ!` | Increments to next string in place | Transform |
| `tr` | Returns copy with character transliteration applied | Transform |
| `tr!` | Applies character transliteration in place | Transform |
| `tr_s` | Transliterates and squeezes duplicate results | Transform |
| `tr_s!` | Transliterates and squeezes in place | Transform |

### Iteration

| Method | Description | Category |
|--------|-------------|----------|
| `chars` | Returns array of characters | Iteration |
| `codepoints` | Returns array of integer codepoints | Iteration |
| `each_byte` | Iterates over each byte as integer | Iteration |
| `each_char` | Iterates over each character as string | Iteration |
| `each_codepoint` | Iterates over each integer codepoint | Iteration |
| `each_grapheme_cluster` | Iterates over each grapheme cluster | Iteration |
| `each_line` | Iterates over each line using separator | Iteration |
| `grapheme_clusters` | Returns array of grapheme clusters | Iteration |
| `lines` | Returns array of lines using separator | Iteration |
| `upto` | Iterates from self to other string in sequence | Iteration |

### Conversion

| Method | Description | Category |
|--------|-------------|----------|
| `dump` | Returns quoted, escaped version for debugging | Conversion |
| `freeze` | Prevents further modification of string | State |
| `frozen?` | Returns true if string is frozen/immutable | State |
| `hex` | Interprets string as hex, returns integer | Conversion |
| `inspect` | Returns printable version with escapes shown | Conversion |
| `intern` | Converts string to Symbol (alias of to_sym) | Conversion |
| `oct` | Interprets string as octal, returns integer | Conversion |
| `to_c` | Converts string to Complex number | Conversion |
| `to_f` | Converts string to Float | Conversion |
| `to_i` | Converts string to Integer in given base | Conversion |
| `to_r` | Converts string to Rational number | Conversion |
| `to_s` | Returns self (string is already a string) | Conversion |
| `to_str` | Returns self (implicit string conversion) | Conversion |
| `to_sym` | Converts string to Symbol | Conversion |
| `undump` | Reverses dump, returns unescaped string | Conversion |

### Size & Splitting

| Method | Description | Category |
|--------|-------------|----------|
| `length` | Returns number of characters in string | Size |
| `size` | Returns number of characters (alias of length) | Size |
| `partition` | Splits at first match into [before, match, after] | Split |
| `rpartition` | Splits at last match into [before, match, after] | Split |
| `slice` | Returns substring (same as []) | Access |
| `slice!` | Removes and returns substring from self | Access |
| `split` | Divides string into array using delimiter/pattern | Split |

### Packing & Miscellaneous

| Method | Description | Category |
|--------|-------------|----------|
| `crypt` | One-way cryptographic hash (DES/MD5/SHA, deprecated) | Misc |
| `pack` | Packs array of values into binary string (Array method) | Pack |
| `sum` | Returns basic checksum (sum of bytes modulo 2^bits) | Misc |
| `unpack` | Decodes binary string into array per template | Pack |
| `unpack1` | Decodes first value from binary string per template | Pack |

---

## 2. File/IO Methods

### File Class Methods (Static)

| Method | Description | Category |
|--------|-------------|----------|
| `File.open` | Opens file with mode/permissions, yields to block if given | Open |
| `File.new` | Creates new File object (prefer open with block) | Open |
| `File.read` | Reads entire file contents as string | Read |
| `File.write` | Writes string to file, returns bytes written | Write |
| `File.readlines` | Reads file into array of lines | Read |
| `File.foreach` | Iterates over each line of file | Read |
| `File.binread` | Reads file in binary mode as string | Read |
| `File.binwrite` | Writes to file in binary mode | Write |
| `File.exist?` | Returns true if file exists at path | Query |
| `File.exists?` | Deprecated alias for exist? | Query |
| `File.file?` | Returns true if path is a regular file | Query |
| `File.directory?` | Returns true if path is a directory | Query |
| `File.symlink?` | Returns true if path is a symbolic link | Query |
| `File.pipe?` | Returns true if path is a named pipe (FIFO) | Query |
| `File.socket?` | Returns true if path is a socket | Query |
| `File.blockdev?` | Returns true if path is a block device | Query |
| `File.chardev?` | Returns true if path is a character device | Query |
| `File.readable?` | Returns true if file is readable by effective user | Query |
| `File.writable?` | Returns true if file is writable by effective user | Query |
| `File.executable?` | Returns true if file is executable by effective user | Query |
| `File.owned?` | Returns true if file is owned by effective user | Query |
| `File.size` | Returns file size in bytes | Query |
| `File.size?` | Returns file size if > 0, nil otherwise | Query |
| `File.zero?` | Returns true if file exists and has zero size | Query |
| `File.empty?` | Alias for zero? | Query |
| `File.delete` | Deletes named files, returns count deleted | Modify |
| `File.unlink` | Alias for delete | Modify |
| `File.rename` | Renames file from old path to new path | Modify |
| `File.chmod` | Changes permission bits on named files | Modify |
| `File.chown` | Changes owner and group of named files | Modify |
| `File.chmod` | Changes permission mode of files | Modify |
| `File.stat` | Returns File::Stat object with file information | Info |
| `File.lstat` | Like stat but doesn't follow symlinks | Info |
| `File.mtime` | Returns last modification time as Time object | Info |
| `File.atime` | Returns last access time as Time object | Info |
| `File.ctime` | Returns last change time (inode) as Time object | Info |
| `File.birthtime` | Returns creation time as Time object | Info |
| `File.ftype` | Returns file type as string ("file", "directory", etc.) | Info |
| `File.basename` | Returns last component of path, optionally removing suffix | Path |
| `File.dirname` | Returns directory portion of path | Path |
| `File.extname` | Returns file extension including dot | Path |
| `File.expand_path` | Converts to absolute path, expanding ~ and relative | Path |
| `File.join` | Joins path components with File::SEPARATOR | Path |
| `File.split` | Returns [dirname, basename] array | Path |
| `File.absolute_path` | Converts to absolute path (doesn't expand ~) | Path |
| `File.realpath` | Returns real (canonical) path resolving symlinks | Path |
| `File.realdirpath` | Like realpath but last component needn't exist | Path |
| `File.fnmatch` | Tests path against shell glob pattern | Path |
| `File.fnmatch?` | Alias for fnmatch | Path |
| `File.glob` | (Delegated to Dir.glob) Returns matching file paths | Path |
| `File.symlink` | Creates symbolic link from old to new path | Link |
| `File.link` | Creates hard link from old to new path | Link |
| `File.readlink` | Returns target of symbolic link | Link |
| `File.truncate` | Truncates file to specified byte length | Modify |
| `File.identical?` | Returns true if two paths refer to same file | Query |
| `File.utime` | Sets access and modification times on files | Modify |
| `File.umask` | Gets/sets file creation permission mask | Modify |
| `File.world_readable?` | Returns permission bits if world-readable, nil otherwise | Query |
| `File.world_writable?` | Returns permission bits if world-writable, nil otherwise | Query |
| `File.sticky?` | Returns true if sticky bit is set | Query |
| `File.setuid?` | Returns true if setuid bit is set | Query |
| `File.setgid?` | Returns true if setgid bit is set | Query |
| `File.grpowned?` | Returns true if file group matches effective group | Query |

### File Instance Methods

| Method | Description | Category |
|--------|-------------|----------|
| `read` | Reads length bytes from current position | Read |
| `read_nonblock` | Reads bytes without blocking, raises on would-block | Read |
| `readline` | Reads next line, raises EOFError at end | Read |
| `readlines` | Reads remaining lines into array | Read |
| `readchar` | Reads next character, raises EOFError at end | Read |
| `readbyte` | Reads next byte as integer, raises EOFError at end | Read |
| `readpartial` | Reads at most maxlen bytes, blocks minimally | Read |
| `gets` | Reads next line, returns nil at end | Read |
| `getc` | Reads next character, returns nil at end | Read |
| `getbyte` | Reads next byte as integer, returns nil at end | Read |
| `write` | Writes string to file, returns bytes written | Write |
| `write_nonblock` | Writes without blocking, raises on would-block | Write |
| `puts` | Writes objects followed by newline | Write |
| `print` | Writes objects without trailing newline | Write |
| `printf` | Writes formatted string using format specifiers | Write |
| `putc` | Writes single character to file | Write |
| `<<` | Writes object to IO (returns self for chaining) | Write |
| `sysread` | Reads bytes using low-level system call | Read |
| `syswrite` | Writes bytes using low-level system call | Write |
| `pread` | Reads from offset without changing file position | Read |
| `pwrite` | Writes at offset without changing file position | Write |
| `seek` | Moves file position to offset with whence | Position |
| `tell` | Returns current byte position in file | Position |
| `pos` | Returns current byte position (alias of tell) | Position |
| `pos=` | Sets file position to given byte offset | Position |
| `rewind` | Moves position to beginning of file, resets lineno | Position |
| `eof?` | Returns true if at end of file | Position |
| `eof` | Alias for eof? | Position |
| `close` | Closes the file stream | Lifecycle |
| `closed?` | Returns true if file is closed | Lifecycle |
| `close_read` | Closes read end of duplex stream | Lifecycle |
| `close_write` | Closes write end of duplex stream | Lifecycle |
| `flush` | Flushes buffered data to OS | Lifecycle |
| `fsync` | Flushes data to disk (bypasses OS buffer) | Lifecycle |
| `fdatasync` | Flushes data to disk (metadata may lag) | Lifecycle |
| `sync` | Returns current sync mode (true = auto-flush) | Lifecycle |
| `sync=` | Sets sync mode for automatic flushing | Lifecycle |
| `stat` | Returns File::Stat for this open file | Info |
| `path` | Returns path string used to open the file | Info |
| `to_path` | Returns path (alias for path) | Info |
| `fileno` | Returns integer file descriptor | Info |
| `to_i` | Returns integer file descriptor (alias of fileno) | Info |
| `truncate` | Truncates file to specified byte length | Modify |
| `flock` | Applies or removes advisory file lock | Modify |
| `each` | Iterates over each line (alias of each_line) | Iteration |
| `each_line` | Iterates over each line with separator | Iteration |
| `each_byte` | Iterates over each byte as integer | Iteration |
| `each_char` | Iterates over each character as string | Iteration |
| `each_codepoint` | Iterates over each codepoint as integer | Iteration |
| `lineno` | Returns current line number | Info |
| `lineno=` | Sets current line number | Info |
| `isatty` | Returns true if IO is a terminal/TTY | Info |
| `tty?` | Alias for isatty | Info |
| `binmode` | Puts stream into binary mode | Mode |
| `binmode?` | Returns true if stream is in binary mode | Mode |
| `autoclose?` | Returns true if FD auto-closes on GC | Mode |
| `autoclose=` | Sets whether FD auto-closes | Mode |
| `close_on_exec?` | Returns close-on-exec flag | Mode |
| `close_on_exec=` | Sets close-on-exec flag | Mode |
| `set_encoding` | Sets external and internal encoding | Mode |
| `external_encoding` | Returns the external Encoding | Mode |
| `internal_encoding` | Returns the internal Encoding | Mode |
| `ungetc` | Pushes character back into input buffer | Read |
| `ungetbyte` | Pushes byte back into input buffer | Read |

### IO Class Methods (Inherited by File)

| Method | Description | Category |
|--------|-------------|----------|
| `IO.read` | Opens file, reads content, closes (convenience) | Read |
| `IO.write` | Opens file, writes content, closes (convenience) | Write |
| `IO.readlines` | Opens file, reads all lines, closes | Read |
| `IO.foreach` | Opens file, yields each line, closes | Read |
| `IO.popen` | Runs command, returns IO connected to process | Process |
| `IO.pipe` | Creates connected read/write IO pair | Process |
| `IO.select` | Monitors multiple IOs for readiness | Process |
| `IO.copy_stream` | Copies data between IO streams efficiently | Process |
| `IO.sysopen` | Opens path at OS level, returns file descriptor | Open |
| `IO.for_fd` | Creates IO wrapper around existing file descriptor | Open |
| `IO.try_convert` | Attempts to convert object to IO | Conversion |
| `IO.console` | Returns IO for the console (stdin/stdout) | Console |

### Dir Class Methods

| Method | Description | Category |
|--------|-------------|----------|
| `Dir.glob` | Returns array of filenames matching pattern | Search |
| `Dir[]` | Shorthand for Dir.glob | Search |
| `Dir.entries` | Returns array of all entries including . and .. | List |
| `Dir.children` | Returns array of entries excluding . and .. | List |
| `Dir.each_child` | Iterates over entries excluding . and .. | List |
| `Dir.foreach` | Iterates over all entries including . and .. | List |
| `Dir.exist?` | Returns true if directory exists at path | Query |
| `Dir.exists?` | Deprecated alias for exist? | Query |
| `Dir.empty?` | Returns true if directory has no entries | Query |
| `Dir.mkdir` | Creates directory with optional permissions | Create |
| `Dir.rmdir` | Removes empty directory | Remove |
| `Dir.delete` | Alias for rmdir | Remove |
| `Dir.unlink` | Alias for rmdir | Remove |
| `Dir.chdir` | Changes working directory, yields to block if given | Navigate |
| `Dir.pwd` | Returns current working directory as string | Navigate |
| `Dir.getwd` | Alias for pwd | Navigate |
| `Dir.home` | Returns home directory for user or current user | Navigate |
| `Dir.tmpdir` | Returns system temporary directory path | Navigate |
| `Dir.new` | Opens directory for reading entries | Open |
| `Dir.open` | Opens directory, yields to block if given | Open |

### Dir Instance Methods

| Method | Description | Category |
|--------|-------------|----------|
| `read` | Returns next entry name or nil at end | Read |
| `each` | Iterates over each entry name | Iteration |
| `rewind` | Repositions to first entry | Position |
| `seek` | Moves to position previously returned by tell | Position |
| `tell` | Returns current position in directory stream | Position |
| `pos` | Alias for tell | Position |
| `pos=` | Sets position in directory stream | Position |
| `close` | Closes directory stream | Lifecycle |
| `path` | Returns path used to open directory | Info |
| `to_path` | Alias for path | Info |
| `inspect` | Returns string representation | Info |
| `fileno` | Returns file descriptor of directory stream | Info |
| `children` | Returns array of entries excluding . and .. | List |

### FileUtils Module Methods

| Method | Description | Category |
|--------|-------------|----------|
| `FileUtils.cp` | Copies file(s) to destination | Copy |
| `FileUtils.copy` | Alias for cp | Copy |
| `FileUtils.cp_r` | Copies files/directories recursively | Copy |
| `FileUtils.cp_lr` | Copies directory structure with hard links | Copy |
| `FileUtils.mv` | Moves file(s) to destination | Move |
| `FileUtils.move` | Alias for mv | Move |
| `FileUtils.rm` | Removes file(s) | Remove |
| `FileUtils.remove` | Alias for rm | Remove |
| `FileUtils.rm_r` | Removes files/directories recursively | Remove |
| `FileUtils.rm_f` | Removes files forcefully (no error on missing) | Remove |
| `FileUtils.rm_rf` | Removes recursively and forcefully | Remove |
| `FileUtils.safe_unlink` | Alias for rm_f | Remove |
| `FileUtils.mkdir` | Creates directory(ies) | Create |
| `FileUtils.makedirs` | Alias for mkdir_p | Create |
| `FileUtils.mkdir_p` | Creates directory and all parents | Create |
| `FileUtils.mkpath` | Alias for mkdir_p | Create |
| `FileUtils.rmdir` | Removes empty directory(ies) | Remove |
| `FileUtils.touch` | Updates timestamps, creates if missing | Modify |
| `FileUtils.chmod` | Changes file permissions | Modify |
| `FileUtils.chmod_R` | Changes permissions recursively | Modify |
| `FileUtils.chown` | Changes file owner and group | Modify |
| `FileUtils.chown_R` | Changes owner/group recursively | Modify |
| `FileUtils.ln` | Creates hard link(s) | Link |
| `FileUtils.link` | Alias for ln | Link |
| `FileUtils.ln_s` | Creates symbolic link(s) | Link |
| `FileUtils.symlink` | Alias for ln_s | Link |
| `FileUtils.ln_sf` | Creates symbolic link forcefully (overwrites) | Link |
| `FileUtils.compare_file` | Returns true if two files have same content | Compare |
| `FileUtils.cmp` | Alias for compare_file | Compare |
| `FileUtils.identical?` | Alias for compare_file | Compare |
| `FileUtils.compare_stream` | Returns true if two streams have same content | Compare |
| `FileUtils.install` | Copies file with optional permission and backup | Install |
| `FileUtils.uptodate?` | Returns true if target is newer than all sources | Compare |
| `FileUtils.cd` | Changes directory with optional block | Navigate |
| `FileUtils.chdir` | Alias for cd | Navigate |
| `FileUtils.pwd` | Returns current working directory | Navigate |
| `FileUtils.getwd` | Alias for pwd | Navigate |
| `FileUtils.collect_method` | Returns list of methods with specific option | Meta |
| `FileUtils.commands` | Returns list of all FileUtils command names | Meta |
| `FileUtils.have_option?` | Checks if command accepts given option | Meta |
| `FileUtils.options` | Returns list of all options | Meta |
| `FileUtils.options_of` | Returns options accepted by specific command | Meta |

### Pathname Instance Methods

| Method | Description | Category |
|--------|-------------|----------|
| `+` / `join` | Appends path component (returns new Pathname) | Build |
| `/` | Alias for + (append path component) | Build |
| `==` | Compares paths as strings | Compare |
| `<=>` | Spaceship comparison of path strings | Compare |
| `to_s` | Returns path as string | Conversion |
| `to_str` | Implicit string conversion | Conversion |
| `to_path` | Returns path string (for File methods) | Conversion |
| `inspect` | Returns inspectable string representation | Conversion |
| `basename` | Returns last component (delegates to File.basename) | Component |
| `dirname` | Returns parent directory (delegates to File.dirname) | Component |
| `extname` | Returns file extension including dot | Component |
| `parent` | Returns parent directory as Pathname | Component |
| `root?` | Returns true if this is the root path | Query |
| `absolute?` | Returns true if path is absolute | Query |
| `relative?` | Returns true if path is relative | Query |
| `cleanpath` | Returns cleaned path (removes extra /, .., .) | Transform |
| `realpath` | Returns canonical absolute path resolving symlinks | Transform |
| `realdirpath` | Like realpath but last component needn't exist | Transform |
| `expand_path` | Returns absolute path expanding ~ and relative | Transform |
| `relative_path_from` | Returns relative path from given base | Transform |
| `each_filename` | Iterates over each path component | Iteration |
| `descend` | Iterates from root to self through ancestors | Iteration |
| `ascend` | Iterates from self to root through ancestors | Iteration |
| `children` | Returns array of immediate children as Pathnames | Directory |
| `each_child` | Iterates over immediate children | Directory |
| `entries` | Returns directory entries as Pathnames | Directory |
| `glob` | Returns matching children using glob pattern | Directory |
| `mkdir` | Creates directory at this path | Directory |
| `rmdir` | Removes empty directory at this path | Directory |
| `mkpath` | Creates directory and parents | Directory |
| `rmtree` | Removes directory tree recursively | Directory |
| `opendir` | Opens directory for reading | Directory |
| `exist?` | Returns true if path exists | File Query |
| `file?` | Returns true if path is a regular file | File Query |
| `directory?` | Returns true if path is a directory | File Query |
| `symlink?` | Returns true if path is a symbolic link | File Query |
| `pipe?` | Returns true if path is a named pipe | File Query |
| `socket?` | Returns true if path is a socket | File Query |
| `blockdev?` | Returns true if path is a block device | File Query |
| `chardev?` | Returns true if path is a character device | File Query |
| `readable?` | Returns true if file is readable | File Query |
| `writable?` | Returns true if file is writable | File Query |
| `executable?` | Returns true if file is executable | File Query |
| `owned?` | Returns true if file is owned by effective user | File Query |
| `world_readable?` | Returns permission bits if world-readable | File Query |
| `world_writable?` | Returns permission bits if world-writable | File Query |
| `sticky?` | Returns true if sticky bit is set | File Query |
| `setuid?` | Returns true if setuid bit is set | File Query |
| `setgid?` | Returns true if setgid bit is set | File Query |
| `grpowned?` | Returns true if group owned by effective group | File Query |
| `zero?` | Returns true if file exists and is empty | File Query |
| `empty?` | Returns true if file/directory is empty | File Query |
| `size` | Returns file size in bytes | File Info |
| `size?` | Returns size if > 0, nil otherwise | File Info |
| `stat` | Returns File::Stat object | File Info |
| `lstat` | Returns File::Stat without following symlinks | File Info |
| `ftype` | Returns type string ("file", "directory", etc.) | File Info |
| `atime` | Returns last access time | File Info |
| `mtime` | Returns last modification time | File Info |
| `ctime` | Returns last change time | File Info |
| `birthtime` | Returns creation time | File Info |
| `read` | Reads entire file content | File IO |
| `binread` | Reads file in binary mode | File IO |
| `write` | Writes content to file | File IO |
| `binwrite` | Writes to file in binary mode | File IO |
| `readlines` | Reads file into array of lines | File IO |
| `each_line` | Iterates over each line of file | File IO |
| `open` | Opens file with mode, yields to block | File IO |
| `rename` | Renames file to given path | File Ops |
| `delete` | Deletes file | File Ops |
| `unlink` | Alias for delete | File Ops |
| `chmod` | Changes file permissions | File Ops |
| `chown` | Changes file owner/group | File Ops |
| `truncate` | Truncates file to given size | File Ops |
| `utime` | Sets access and modification times | File Ops |
| `make_link` | Creates hard link to target | Link |
| `make_symlink` | Creates symbolic link to target | Link |
| `readlink` | Returns target of symbolic link | Link |
| `split` | Returns [dirname, basename] as Pathnames | Component |
| `sub` | Substitutes pattern in path string | Transform |
| `sub_ext` | Substitutes file extension | Transform |
| `fnmatch` | Tests path against glob pattern | Query |
| `fnmatch?` | Alias for fnmatch | Query |
| `freeze` | Freezes the Pathname object | State |
| `frozen?` | Returns true if Pathname is frozen | State |
| `hash` | Returns hash value for use as Hash key | State |
| `taint` | Taints the pathname (deprecated in Ruby 2.7+) | State |
| `untaint` | Untaints the pathname (deprecated) | State |

---

## 3. Collection Methods

### Array Methods

#### Adding & Removing Elements

| Method | Description | Category |
|--------|-------------|----------|
| `push` | Appends one or more elements to end of array | Add |
| `append` | Alias for push | Add |
| `<<` | Appends single element to end (returns self) | Add |
| `unshift` | Prepends one or more elements to beginning | Add |
| `prepend` | Alias for unshift | Add |
| `insert` | Inserts elements before index position | Add |
| `pop` | Removes and returns last element(s) | Remove |
| `shift` | Removes and returns first element(s) | Remove |
| `delete` | Removes all occurrences of value, returns it or nil | Remove |
| `delete_at` | Removes element at index, returns it or nil | Remove |
| `delete_if` | Removes elements for which block returns true | Remove |
| `keep_if` | Keeps only elements for which block returns true | Remove |
| `clear` | Removes all elements from array | Remove |
| `compact` | Returns copy without nil elements | Remove |
| `compact!` | Removes nil elements in place | Remove |
| `uniq` | Returns copy without duplicate elements | Remove |
| `uniq!` | Removes duplicates in place | Remove |
| `reject` | Returns new array without elements matching block | Remove |
| `reject!` | Removes elements matching block in place | Remove |

#### Operators

| Method | Description | Category |
|--------|-------------|----------|
| `+` | Concatenates two arrays, returns new array | Operator |
| `-` | Returns new array with elements from other removed | Operator |
| `&` | Returns intersection (common elements, no duplicates) | Operator |
| `\|` | Returns union (all elements, no duplicates) | Operator |
| `*` | Repeats array n times or joins with string separator | Operator |
| `<=>` | Spaceship comparison of arrays element by element | Operator |
| `==` | Returns true if arrays have same length and elements | Operator |

#### Access & Search

| Method | Description | Category |
|--------|-------------|----------|
| `[]` | Returns element or subarray by index/range | Access |
| `[]=` | Sets element or subarray by index/range | Access |
| `at` | Returns element at index (only integer, no range) | Access |
| `fetch` | Returns element at index, raises or uses default on out-of-bounds | Access |
| `first` | Returns first element or first n elements | Access |
| `last` | Returns last element or last n elements | Access |
| `sample` | Returns random element(s) from array | Access |
| `dig` | Extracts nested value by sequence of indices | Access |
| `values_at` | Returns array of elements at given indices | Access |
| `assoc` | Searches array of arrays by first element | Search |
| `rassoc` | Searches array of arrays by second element | Search |
| `bsearch` | Binary search for value in sorted array | Search |
| `bsearch_index` | Binary search returning index in sorted array | Search |
| `include?` | Returns true if array contains element | Search |
| `member?` | Alias for include? | Search |
| `index` | Returns first index of element or block match | Search |
| `find_index` | Alias for index | Search |
| `rindex` | Returns last index of element or block match | Search |

#### Sorting & Reordering

| Method | Description | Category |
|--------|-------------|----------|
| `sort` | Returns sorted copy using <=> or block | Sort |
| `sort!` | Sorts in place | Sort |
| `sort_by` | Returns sorted copy using block-returned keys | Sort |
| `sort_by!` | Sorts in place by block-returned keys | Sort |
| `reverse` | Returns copy with elements in reverse order | Order |
| `reverse!` | Reverses elements in place | Order |
| `rotate` | Returns copy rotated by count positions | Order |
| `rotate!` | Rotates in place by count positions | Order |
| `shuffle` | Returns copy with elements randomly reordered | Order |
| `shuffle!` | Randomly reorders elements in place | Order |
| `flatten` | Returns copy with nested arrays recursively flattened | Transform |
| `flatten!` | Flattens nested arrays in place | Transform |

#### Combining & Splitting

| Method | Description | Category |
|--------|-------------|----------|
| `zip` | Combines with other arrays element by element | Combine |
| `transpose` | Transposes array of arrays (rows to columns) | Combine |
| `combination` | Yields all length-n combinations | Combine |
| `permutation` | Yields all length-n permutations | Combine |
| `repeated_combination` | Yields combinations with repetition | Combine |
| `repeated_permutation` | Yields permutations with repetition | Combine |
| `product` | Returns all combinations of elements from arrays | Combine |
| `pack` | Packs array values into binary string per template | Combine |
| `join` | Joins elements into string with separator | Combine |
| `each_slice` | Iterates over consecutive slices of given size | Split |
| `each_cons` | Iterates over consecutive overlapping groups | Split |
| `partition` | Splits into two arrays: matches and non-matches | Split |
| `intersection` | Returns array of common elements with other arrays | Set |
| `union` | Returns array of unique elements from self and others | Set |
| `difference` | Returns elements not present in any other array | Set |

#### Iteration & Enumeration

| Method | Description | Category |
|--------|-------------|----------|
| `each` | Iterates over each element yielding to block | Iteration |
| `each_with_index` | Iterates yielding element and its index | Iteration |
| `each_with_object` | Iterates yielding element and accumulator object | Iteration |
| `reverse_each` | Iterates in reverse order | Iteration |
| `cycle` | Iterates over elements n times or infinitely | Iteration |
| `map` | Returns new array with block applied to each element | Transform |
| `collect` | Alias for map | Transform |
| `map!` | Applies block to each element in place | Transform |
| `collect!` | Alias for map! | Transform |
| `flat_map` | Maps then flattens one level | Transform |
| `collect_concat` | Alias for flat_map | Transform |
| `filter_map` | Maps and removes nil results in one pass | Transform |
| `select` | Returns array of elements for which block is true | Filter |
| `filter` | Alias for select | Filter |
| `select!` | Keeps only elements for which block is true, in place | Filter |
| `filter!` | Alias for select! | Filter |
| `detect` | Returns first element for which block is true | Filter |
| `find` | Alias for detect | Filter |

#### Aggregation & Testing

| Method | Description | Category |
|--------|-------------|----------|
| `count` | Returns count of elements (optionally matching value/block) | Aggregate |
| `length` | Returns number of elements | Aggregate |
| `size` | Alias for length | Aggregate |
| `empty?` | Returns true if array has no elements | Test |
| `any?` | Returns true if any element matches block/pattern | Test |
| `all?` | Returns true if all elements match block/pattern | Test |
| `none?` | Returns true if no elements match block/pattern | Test |
| `one?` | Returns true if exactly one element matches | Test |
| `min` | Returns minimum element | Aggregate |
| `max` | Returns maximum element | Aggregate |
| `min_by` | Returns element with minimum block result | Aggregate |
| `max_by` | Returns element with maximum block result | Aggregate |
| `minmax` | Returns [min, max] pair | Aggregate |
| `minmax_by` | Returns [min, max] by block result | Aggregate |
| `sum` | Returns sum of elements (with optional initial value) | Aggregate |
| `tally` | Returns hash counting occurrences of each element | Aggregate |
| `reduce` | Combines elements using block or symbol operator | Aggregate |
| `inject` | Alias for reduce | Aggregate |

#### Grouping & Chunking

| Method | Description | Category |
|--------|-------------|----------|
| `group_by` | Returns hash grouping elements by block result | Group |
| `chunk` | Groups consecutive elements by block result | Group |
| `chunk_while` | Groups consecutive elements while block is true | Group |
| `slice_when` | Splits between elements where block is true | Group |
| `slice_before` | Splits before elements matching pattern/block | Group |
| `slice_after` | Splits after elements matching pattern/block | Group |

#### Taking & Dropping

| Method | Description | Category |
|--------|-------------|----------|
| `take` | Returns first n elements | Subset |
| `take_while` | Returns leading elements while block is true | Subset |
| `drop` | Returns array without first n elements | Subset |
| `drop_while` | Returns array without leading matching elements | Subset |

#### Conversion & Misc

| Method | Description | Category |
|--------|-------------|----------|
| `to_a` | Returns self (array is already an array) | Conversion |
| `to_ary` | Returns self (implicit array conversion) | Conversion |
| `to_h` | Converts array of [key, value] pairs to Hash | Conversion |
| `to_set` | Converts to Set (requires 'set') | Conversion |
| `replace` | Replaces contents with another array | Misc |
| `fill` | Fills array with value or block result | Misc |
| `concat` | Appends elements from other arrays to self | Misc |
| `slice` | Returns element or subarray (same as []) | Misc |
| `slice!` | Removes and returns subarray | Misc |
| `each_index` | Iterates yielding each index | Iteration |
| `frozen?` | Returns true if array is frozen | State |
| `hash` | Returns hash value | State |
| `inspect` | Returns printable string representation | Conversion |
| `to_s` | Alias for inspect | Conversion |
| `abbrev` | Returns hash of unambiguous abbreviations (require 'abbrev') | Misc |

---

### Hash Methods

#### Access & Assignment

| Method | Description | Category |
|--------|-------------|----------|
| `[]` | Returns value for key, or default | Access |
| `[]=` | Sets value for key | Access |
| `fetch` | Returns value for key, raises or uses default if missing | Access |
| `fetch_values` | Returns array of values for given keys, raises if missing | Access |
| `store` | Sets value for key (alias of []=) | Access |
| `values_at` | Returns array of values for given keys | Access |
| `dig` | Extracts nested value by sequence of keys | Access |
| `default` | Returns default value for missing keys | Access |
| `default=` | Sets default value for missing keys | Access |
| `default_proc` | Returns default proc for missing keys | Access |
| `default_proc=` | Sets default proc for missing keys | Access |

#### Keys & Values

| Method | Description | Category |
|--------|-------------|----------|
| `keys` | Returns array of all keys | Access |
| `values` | Returns array of all values | Access |
| `has_key?` | Returns true if hash contains key | Query |
| `key?` | Alias for has_key? | Query |
| `include?` | Alias for has_key? | Query |
| `member?` | Alias for has_key? | Query |
| `has_value?` | Returns true if hash contains value | Query |
| `value?` | Alias for has_value? | Query |
| `key` | Returns key for given value, or nil | Query |
| `assoc` | Returns [key, value] pair for matching key | Query |
| `rassoc` | Returns [key, value] pair for matching value | Query |

#### Deletion & Filtering

| Method | Description | Category |
|--------|-------------|----------|
| `delete` | Removes key-value pair, returns value or nil | Remove |
| `delete_if` | Removes pairs for which block returns true | Remove |
| `keep_if` | Keeps only pairs for which block returns true | Remove |
| `reject` | Returns new hash without pairs matching block | Filter |
| `reject!` | Removes matching pairs in place, returns nil if none | Filter |
| `select` | Returns new hash with pairs matching block | Filter |
| `filter` | Alias for select | Filter |
| `select!` | Keeps matching pairs in place | Filter |
| `filter!` | Alias for select! | Filter |
| `compact` | Returns new hash without nil values | Filter |
| `compact!` | Removes nil values in place | Filter |
| `clear` | Removes all key-value pairs | Remove |
| `slice` | Returns hash with only specified keys | Filter |
| `except` | Returns hash without specified keys (Ruby 3.0+) | Filter |

#### Iteration

| Method | Description | Category |
|--------|-------------|----------|
| `each` | Iterates over each [key, value] pair | Iteration |
| `each_pair` | Alias for each | Iteration |
| `each_key` | Iterates over each key | Iteration |
| `each_value` | Iterates over each value | Iteration |
| `each_with_object` | Iterates yielding pair and accumulator object | Iteration |

#### Transformation

| Method | Description | Category |
|--------|-------------|----------|
| `map` | Returns array of block results for each pair | Transform |
| `collect` | Alias for map | Transform |
| `flat_map` | Maps then flattens one level | Transform |
| `filter_map` | Maps and removes nil results (Ruby 2.7+) | Transform |
| `transform_keys` | Returns hash with keys modified by block | Transform |
| `transform_keys!` | Modifies keys in place | Transform |
| `transform_values` | Returns hash with values modified by block | Transform |
| `transform_values!` | Modifies values in place | Transform |
| `invert` | Returns hash with keys and values swapped | Transform |
| `flatten` | Returns flat array of keys and values | Transform |
| `to_a` | Returns array of [key, value] pairs | Conversion |
| `to_h` | Returns self or applies block to pairs | Conversion |

#### Merging & Combining

| Method | Description | Category |
|--------|-------------|----------|
| `merge` | Returns new hash merging other hash(es), block resolves conflicts | Merge |
| `merge!` | Merges other hash(es) in place | Merge |
| `update` | Alias for merge! | Merge |
| `replace` | Replaces contents with another hash | Merge |

#### Aggregation & Testing

| Method | Description | Category |
|--------|-------------|----------|
| `empty?` | Returns true if hash has no pairs | Test |
| `size` | Returns number of key-value pairs | Aggregate |
| `length` | Alias for size | Aggregate |
| `count` | Returns count of pairs (optionally matching block) | Aggregate |
| `any?` | Returns true if any pair matches block | Test |
| `all?` | Returns true if all pairs match block | Test |
| `none?` | Returns true if no pairs match block | Test |
| `min_by` | Returns pair with minimum block result | Aggregate |
| `max_by` | Returns pair with maximum block result | Aggregate |
| `sort_by` | Returns sorted array of pairs by block result | Aggregate |
| `group_by` | Returns hash grouping pairs by block result | Aggregate |
| `sum` | Returns sum of block results for each pair | Aggregate |
| `reduce` | Combines pairs using accumulator and block | Aggregate |
| `inject` | Alias for reduce | Aggregate |

#### Misc

| Method | Description | Category |
|--------|-------------|----------|
| `frozen?` | Returns true if hash is frozen | State |
| `hash` | Returns hash value for the hash itself | State |
| `inspect` | Returns printable string representation | Conversion |
| `to_s` | Alias for inspect | Conversion |
| `to_proc` | Returns proc that maps keys to values | Conversion |
| `compare_by_identity` | Uses object identity instead of eql? for keys | Config |
| `compare_by_identity?` | Returns true if using identity comparison | Config |
| `rehash` | Rebuilds hash table after key mutation | Config |
| `eql?` | Returns true if hashes have same content | Compare |

---

### Set Methods

(Requires `require 'set'`; built-in since Ruby 3.2)

| Method | Description | Category |
|--------|-------------|----------|
| `add` | Adds element to set, returns self | Add |
| `<<` | Alias for add | Add |
| `add?` | Adds element, returns self if new or nil if present | Add |
| `delete` | Removes element from set, returns self | Remove |
| `delete?` | Removes element, returns self if found or nil | Remove |
| `delete_if` | Removes elements for which block returns true | Remove |
| `keep_if` | Keeps only elements for which block returns true | Remove |
| `reject!` | Removes matching elements in place | Remove |
| `select!` | Keeps matching elements in place (alias: filter!) | Remove |
| `clear` | Removes all elements from set | Remove |
| `include?` | Returns true if set contains element | Query |
| `member?` | Alias for include? | Query |
| `===` | Alias for include? (for use in case/when) | Query |
| `empty?` | Returns true if set has no elements | Query |
| `size` | Returns number of elements | Info |
| `length` | Alias for size | Info |
| `each` | Iterates over each element | Iteration |
| `map` | Returns new Set with block applied to each element | Transform |
| `collect` | Alias for map | Transform |
| `select` | Returns new Set with elements matching block | Filter |
| `filter` | Alias for select | Filter |
| `reject` | Returns new Set without elements matching block | Filter |
| `flat_map` | Maps then flattens, returns new Set | Transform |
| `collect_concat` | Alias for flat_map | Transform |
| `flatten` | Returns new Set with nested Sets flattened | Transform |
| `flatten!` | Flattens nested Sets in place | Transform |
| `classify` | Returns hash grouping elements by block result | Group |
| `divide` | Divides set into subsets by equivalence block | Group |
| `merge` | Adds all elements from enumerable to self | Set Ops |
| `subtract` | Removes all elements in enumerable from self | Set Ops |
| `&` | Returns intersection of two sets | Set Ops |
| `intersection` | Alias for & | Set Ops |
| `\|` | Returns union of two sets | Set Ops |
| `union` | Alias for \| | Set Ops |
| `+` | Alias for \| (union) | Set Ops |
| `-` | Returns difference (elements in self not in other) | Set Ops |
| `difference` | Alias for - | Set Ops |
| `^` | Returns symmetric difference (XOR) | Set Ops |
| `subset?` | Returns true if self is subset of other | Set Test |
| `<=` | Alias for subset? | Set Test |
| `proper_subset?` | Returns true if self is strict subset of other | Set Test |
| `<` | Alias for proper_subset? | Set Test |
| `superset?` | Returns true if self is superset of other | Set Test |
| `>=` | Alias for superset? | Set Test |
| `proper_superset?` | Returns true if self is strict superset of other | Set Test |
| `>` | Alias for proper_superset? | Set Test |
| `intersect?` | Returns true if sets share any elements | Set Test |
| `disjoint?` | Returns true if sets share no elements | Set Test |
| `to_a` | Returns array of all elements | Conversion |
| `to_set` | Returns self or new set (optionally with different class) | Conversion |
| `inspect` | Returns printable string representation | Conversion |
| `to_s` | Alias for inspect | Conversion |
| `reset` | Resets internal hash after element mutation | Config |
| `replace` | Replaces contents with elements from enumerable | Config |
| `freeze` | Freezes set preventing modification | State |
| `frozen?` | Returns true if set is frozen | State |
| `compare_by_identity` | Uses object identity for element comparison | Config |
| `compare_by_identity?` | Returns true if using identity comparison | Config |
| `count` | Returns count of elements matching block | Aggregate |
| `any?` | Returns true if any element matches | Test |
| `all?` | Returns true if all elements match | Test |
| `none?` | Returns true if no elements match | Test |
| `one?` | Returns true if exactly one matches | Test |
| `min` | Returns minimum element | Aggregate |
| `max` | Returns maximum element | Aggregate |
| `min_by` | Returns element with minimum block result | Aggregate |
| `max_by` | Returns element with maximum block result | Aggregate |
| `minmax` | Returns [min, max] pair | Aggregate |
| `sum` | Returns sum of elements | Aggregate |
| `reduce` | Combines elements using accumulator | Aggregate |
| `inject` | Alias for reduce | Aggregate |
| `find` | Returns first matching element | Filter |
| `detect` | Alias for find | Filter |
| `group_by` | Returns hash grouping by block result | Group |
| `sort` | Returns sorted array | Sort |
| `sort_by` | Returns sorted array by block result | Sort |
| `zip` | Combines with other enumerables element-wise | Combine |
| `take` | Returns first n elements as array | Subset |
| `drop` | Returns elements after first n as array | Subset |
| `each_with_index` | Iterates yielding element and index | Iteration |
| `each_with_object` | Iterates yielding element and accumulator | Iteration |

---

### Enumerable Module (Shared Methods)

These methods are available on any class that includes Enumerable and defines `each`:
Array, Hash, Set, Range, Enumerator, IO, Dir, StringIO, and custom classes.

| Method | Description | Category |
|--------|-------------|----------|
| `all?` | Returns true if all elements satisfy condition | Test |
| `any?` | Returns true if at least one element satisfies condition | Test |
| `none?` | Returns true if no elements satisfy condition | Test |
| `one?` | Returns true if exactly one element satisfies condition | Test |
| `count` | Returns count of elements (optionally matching value/block) | Aggregate |
| `sum` | Returns sum of elements or block results | Aggregate |
| `min` | Returns minimum element using <=> or block | Aggregate |
| `max` | Returns maximum element using <=> or block | Aggregate |
| `min_by` | Returns element with minimum block result | Aggregate |
| `max_by` | Returns element with maximum block result | Aggregate |
| `minmax` | Returns [min, max] pair | Aggregate |
| `minmax_by` | Returns [min, max] by block result | Aggregate |
| `sort` | Returns sorted array using <=> or block | Sort |
| `sort_by` | Returns sorted array by block-returned keys | Sort |
| `map` | Returns array of block results | Transform |
| `collect` | Alias for map | Transform |
| `flat_map` | Maps then flattens one level | Transform |
| `collect_concat` | Alias for flat_map | Transform |
| `filter_map` | Maps and removes nil results (Ruby 2.7+) | Transform |
| `select` | Returns array of elements matching block | Filter |
| `filter` | Alias for select | Filter |
| `reject` | Returns array of elements not matching block | Filter |
| `find` | Returns first element matching block | Filter |
| `detect` | Alias for find | Filter |
| `find_index` | Returns index of first matching element | Filter |
| `find_all` | Alias for select | Filter |
| `first` | Returns first element or first n elements | Access |
| `include?` | Returns true if collection contains element | Query |
| `member?` | Alias for include? | Query |
| `each_with_index` | Iterates yielding element and its index | Iteration |
| `each_with_object` | Iterates yielding element and accumulator | Iteration |
| `each_slice` | Iterates over slices of given size | Iteration |
| `each_cons` | Iterates over consecutive overlapping groups | Iteration |
| `each_entry` | Iterates yielding each element (flattens yield args) | Iteration |
| `reverse_each` | Iterates in reverse order | Iteration |
| `cycle` | Iterates over elements n times or infinitely | Iteration |
| `reduce` | Combines all elements using block or named method | Aggregate |
| `inject` | Alias for reduce | Aggregate |
| `each_with_object` | Iterates with memo/accumulator object | Aggregate |
| `group_by` | Returns hash grouping elements by block result | Group |
| `chunk` | Groups consecutive elements returning same block value | Group |
| `chunk_while` | Groups consecutive elements while block returns true | Group |
| `slice_when` | Splits between elements where block returns true | Group |
| `slice_before` | Splits before elements matching pattern/block | Group |
| `slice_after` | Splits after elements matching pattern/block | Group |
| `partition` | Returns two arrays: matching and non-matching | Group |
| `tally` | Returns hash counting occurrences of each element | Group |
| `take` | Returns first n elements | Subset |
| `take_while` | Returns leading elements while block is true | Subset |
| `drop` | Returns all except first n elements | Subset |
| `drop_while` | Drops leading elements while block is true | Subset |
| `zip` | Combines with other enumerables element by element | Combine |
| `flat_map` | Maps and flattens one level | Transform |
| `grep` | Returns elements matching pattern (===) | Filter |
| `grep_v` | Returns elements not matching pattern | Filter |
| `to_a` | Converts to array | Conversion |
| `entries` | Alias for to_a | Conversion |
| `to_h` | Converts to hash (from [key, value] pairs) | Conversion |
| `to_set` | Converts to Set | Conversion |
| `lazy` | Returns lazy enumerator (defers computation) | Lazy |
| `each_slice` | Groups into slices of given size | Chunk |
| `each_cons` | Groups into consecutive overlapping groups | Chunk |
| `uniq` | Returns array of unique elements by block | Transform |

#### Enumerator::Lazy (additional chained methods)

| Method | Description | Category |
|--------|-------------|----------|
| `lazy` | Returns self (already lazy) | Lazy |
| `eager` | Returns non-lazy enumerator | Lazy |
| `force` | Forces evaluation, returns array (alias of to_a) | Lazy |
| `map` | Lazily maps elements | Lazy Transform |
| `select` | Lazily filters elements | Lazy Filter |
| `reject` | Lazily rejects elements | Lazy Filter |
| `flat_map` | Lazily maps and flattens | Lazy Transform |
| `filter_map` | Lazily maps and removes nils | Lazy Transform |
| `take` | Lazily takes first n | Lazy Subset |
| `take_while` | Lazily takes while condition holds | Lazy Subset |
| `drop` | Lazily drops first n | Lazy Subset |
| `drop_while` | Lazily drops while condition holds | Lazy Subset |
| `zip` | Lazily zips enumerables | Lazy Combine |
| `chunk` | Lazily chunks consecutive elements | Lazy Group |
| `chunk_while` | Lazily chunks while condition holds | Lazy Group |
| `slice_when` | Lazily slices between elements | Lazy Group |
| `slice_before` | Lazily slices before matching elements | Lazy Group |
| `slice_after` | Lazily slices after matching elements | Lazy Group |
| `grep` | Lazily filters by pattern | Lazy Filter |
| `grep_v` | Lazily rejects by pattern | Lazy Filter |
| `uniq` | Lazily removes duplicates | Lazy Transform |
| `with_index` | Adds index to each yielded element | Lazy Iteration |

---

## Summary Statistics

| Section | Method Count |
|---------|-------------|
| String | ~128 methods |
| File class methods | ~55 methods |
| File instance methods | ~60 methods |
| IO class methods | ~12 methods |
| Dir class methods | ~20 methods |
| Dir instance methods | ~14 methods |
| FileUtils | ~35 methods |
| Pathname | ~95 methods |
| Array | ~120 methods |
| Hash | ~75 methods |
| Set | ~75 methods |
| Enumerable | ~55 methods |
| Enumerator::Lazy | ~25 methods |
| **Total** | **~769 methods** |
