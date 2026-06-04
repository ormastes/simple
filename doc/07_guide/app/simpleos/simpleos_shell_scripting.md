# SimpleOS Shell Scripting Guide

Shell scripts for SimpleOS use the `.shs` extension and run on the built-in SimpleOS shell (`ShellApp`). The dialect is bash-compatible POSIX sh — scripts written for `/bin/sh` or bash (without heavy bashisms) work with minor caveats.

## Running a Script

```sh
# From the SimpleOS shell prompt
source my_script.shs
. my_script.shs          # same thing

# With arguments
source install.shs --prefix /usr/local
```

Script files are executed via `source` / `.` built-ins, which run the script in the current shell context (variables and functions persist after).

## Variables

```sh
NAME=Alice
GREETING="Hello, ${NAME}"
echo $GREETING             # Hello, Alice

# Unset default
echo ${MISSING:-fallback}  # fallback

# Conditional alternate (only if set)
echo ${NAME:+Hi}           # Hi

# Length
echo ${#NAME}              # 5

# Prefix/suffix stripping
FILE=archive.tar.gz
echo ${FILE#*.}            # tar.gz   (strip shortest prefix match)
echo ${FILE##*.}           # gz       (strip longest prefix match)
echo ${FILE%.gz}           # archive.tar  (strip shortest suffix)
echo ${FILE%%.tar*}        # archive  (strip longest suffix)
```

## Special Variables

| Variable | Meaning |
|----------|---------|
| `$?` | Exit code of last command |
| `$0` | Script name |
| `$1`–`$9` | Positional arguments |
| `$@` | All arguments (space-joined) |
| `$*` | All arguments |
| `$#` | Argument count |

## Command Substitution

```sh
CWD=$(pwd)
HOST=$(hostname)
OS=$(uname -s)
ARCH=$(uname -m)
DIR=$(dirname /usr/local/bin/foo)
BASE=$(basename /usr/local/bin/foo)

# Fast-path built-ins (no subprocess needed):
#   pwd, hostname, uname, uname -s, uname -m,
#   echo <text>, dirname <path>, basename <path>
```

Backtick form also works: `` DIR=`dirname $0` ``

## Control Flow

### if / elif / else

```sh
if [ -f /etc/config ]; then
    echo "config exists"
elif [ -d /etc ]; then
    echo "/etc is a directory"
else
    echo "nothing found"
fi
```

### while loop

```sh
COUNT=0
while [ $COUNT -lt 5 ]; do
    echo $COUNT
    COUNT=$((COUNT + 1))
done
```

### for loop

```sh
for FILE in *.txt; do
    echo "processing $FILE"
done

for ARG in "$@"; do
    echo "arg: $ARG"
done
```

### case

```sh
case $OS in
    Linux)   echo "Linux" ;;
    Darwin)  echo "macOS" ;;
    *)       echo "other" ;;
esac
```

## Boolean Chaining

```sh
# Run next only if previous succeeded
mkdir build && cd build && cmake ..

# Run next only if previous failed
[ -f config.shs ] || cp config.shs.default config.shs
```

## Error Handling

```sh
set -e          # exit immediately on any non-zero exit code
set +e          # disable exit-on-error

# Pattern: run a command, check $? manually
some_command
if [ $? -ne 0 ]; then
    echo "failed" >&2
    exit 1
fi
```

## Functions

```sh
greet() {
    echo "Hello, $1"
}

greet World     # Hello, World
```

## Test / [ Operators

| Operator | Meaning |
|----------|---------|
| `-f FILE` | Regular file exists |
| `-d FILE` | Directory exists |
| `-e FILE` | Path exists (any type) |
| `-s FILE` | File exists and non-empty |
| `-r FILE` | File is readable (stub: true if exists) |
| `-w FILE` | File is writable (stub: true if exists) |
| `-x FILE` | File is executable (stub: true if exists) |
| `-z STR` | String is empty |
| `-n STR` | String is non-empty |
| `A = B` | String equality |
| `A != B` | String inequality |
| `A -eq B` | Integer equal |
| `A -ne B` | Integer not equal |
| `A -lt B` | Integer less-than |
| `A -gt B` | Integer greater-than |
| `! EXPR` | Negate |

## Built-in Commands

| Command | Description |
|---------|-------------|
| `echo` | Print text |
| `printf FORMAT [ARGS...]` | Formatted print |
| `read VAR` | Read line into variable |
| `set -e` / `set +e` | Toggle exit-on-error |
| `export VAR=VAL` | Set environment variable |
| `unset VAR` | Remove variable |
| `alias NAME=CMD` | Define alias |
| `unalias NAME` | Remove alias |
| `shift [N]` | Shift positional args |
| `source FILE` / `. FILE` | Execute script in current shell |
| `cd DIR` | Change directory |
| `pwd` | Print working directory |
| `exit [CODE]` | Exit shell |
| `true` / `false` | Always-succeed / always-fail |
| `env` | Print environment |
| `printenv` | Print environment variables |

## Shell Tools (Coreutils)

Full set available at the prompt and in scripts:

**File I/O:** `cat`, `ls`, `find`, `grep`, `diff`, `patch`  
**Text processing:** `awk`, `sed`, `cut`, `tr`, `sort`, `uniq`, `head`, `tail`, `wc`  
**Reverse/reformat:** `tac`, `rev`, `nl`, `fold`, `column`, `paste`, `comm`, `join`  
**Dump/inspect:** `od`, `hexdump`, `strings`, `file`, `base64`, `md5sum`, `sha256sum`  
**Math/random:** `bc`, `factor`, `shuf`, `expr`, `seq`, `numfmt`  
**File ops:** `cp`, `mv`, `rm`, `mkdir`, `rmdir`, `chmod`, `touch`, `ln`  
**Path utilities:** `basename`, `dirname`, `readlink`, `mktemp`  
**Process/job:** `sleep`, `yes`, `xargs`, `env`, `printenv`

## Starship Prompt

The shell uses a Starship-compatible prompt. Configure it at `~/.config/starship.toml` (key=value format):

```
show_git=true
show_time=false
show_user=true
color_exit=true
```

The prompt shows: exit-code indicator, `user@host`, current directory (with `~` abbreviation), and git branch.

## Known Limitations

- **Here-docs** (`<<EOF`) not yet supported
- **Background jobs** (`cmd &`) are dispatched but not waited on
- **Piping** between commands (`cmd1 | cmd2`) not yet implemented — use temp files
- **`-r`/`-w`/`-x`** file permission tests always return true (VFS doesn't track Unix permissions)
- **`$(cmd)`** for complex commands falls back to capture mode; fast-path covers the common bootstrap patterns
- **`set -u`** (error on unset variables) not implemented
