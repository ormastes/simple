# Directory Privilege Management Scripts

Scripts to manage write permissions on top-level project directories to prevent accidental file creation/deletion at the root level while preserving full access to subdirectories.

## Purpose

Prevent cluttering of important top-level directories (`doc/`, `examples/`, `scripts/`, and project root) by accidentally creating files directly in them, while:
- ✅ Allowing modifications to existing files
- ✅ Allowing full access (create/delete/modify) in subdirectories
- ✅ Maintaining proper directory traversal and read access

## Platform Support

| Platform | Status | Permission Tool | Script Files |
|----------|--------|-----------------|--------------|
| Linux    | ✅ Tested | GNU stat + chmod | `*.sh` |
| macOS    | ✅ Compatible | BSD stat + chmod | `*.sh` |
| FreeBSD  | ✅ Compatible | BSD stat + chmod | `*.sh` |
| Windows  | ✅ Compatible | icacls (NTFS ACLs) | `*.bat` |

**Unix/Linux/macOS**: Shell scripts automatically detect your OS and use the appropriate `stat` command format.

**Windows**: Batch scripts use `icacls` to manage NTFS Access Control Lists (ACLs).

## Scripts

### Unix/Linux/macOS: Shell Scripts

#### `apply_restrictions.sh`
Applies write restrictions to specified directories.

**Usage:**
```bash
sudo ./scripts/privilege/apply_restrictions.sh
```

**What it does:**
- Removes write permission from the directory itself (prevents creating/deleting files directly)
- Preserves read and execute permissions (allows listing and traversal)
- Saves original permissions to `.permissions_backup` for restoration
- Does NOT affect:
  - Existing files (can still be modified)
  - Subdirectories (retain full permissions)
  - File permissions (only directory permissions are changed)

**Protected directories:**
- `.` (project root)
- `doc/`
- `examples/`
- `scripts/`

### `revert_restrictions.sh`
Reverts restrictions and restores original permissions.

**Usage:**
```bash
sudo ./scripts/privilege/revert_restrictions.sh
```

**What it does:**
- Restores permissions from `.permissions_backup`
- Restores ownership if changed
- Removes backup file
- Returns directories to their original state

### Windows: Batch Scripts

#### `apply_restrictions.bat`
Applies write restrictions using Windows NTFS ACLs.

**Usage:**
1. Right-click `scripts\privilege\apply_restrictions.bat`
2. Select "Run as administrator"

**What it does:**
- Adds DENY rules for write permissions (WD, AD, WEA, WA)
- Saves original ACLs to `.permissions_backup.txt` and `.permissions_backup.*.{dir}` files
- Uses `icacls` to manage NTFS permissions
- Does NOT affect:
  - Existing files (can still be modified)
  - Subdirectories (retain full permissions)

**Protected directories:**
- `.` (project root)
- `doc\`
- `examples\`
- `scripts\`

**Permissions denied:**
- `WD` - Write Data (create files)
- `AD` - Append Data (create folders)
- `WEA` - Write Extended Attributes
- `WA` - Write Attributes

#### `revert_restrictions.bat`
Reverts restrictions and restores original NTFS ACLs.

**Usage:**
1. Right-click `scripts\privilege\revert_restrictions.bat`
2. Select "Run as administrator"

**What it does:**
- Removes DENY rules from directories
- Restores original ACLs from backup files
- Removes all backup files
- Returns directories to their original state

## Examples

### Unix/Linux/macOS Examples

### Apply restrictions
```bash
$ sudo ./scripts/privilege/apply_restrictions.sh

=== Simple Project Directory Protection ===
Project root: /home/user/simple

Applying restrictions to prevent file creation/deletion in:
  - Project root (.)
  - doc/
  - examples/
  - scripts/

Saving current permissions...
Backup saved to: scripts/privilege/.permissions_backup

Applying restrictions...
  ✓ Project root: removed write permission
  ✓ doc/: removed write permission
  ✓ examples/: removed write permission
  ✓ scripts/: removed write permission

=== Restrictions Applied Successfully ===
```

### Test restrictions
```bash
# This will FAIL (good!)
$ touch doc/newfile.txt
touch: cannot touch 'doc/newfile.txt': Permission denied

# This will SUCCEED (subdirectories are writable)
$ touch doc/guide/newfile.txt
[OK]

# This will SUCCEED (existing files are modifiable)
$ echo "test" >> doc/README.md
[OK]
```

### Revert restrictions
```bash
$ sudo ./scripts/privilege/revert_restrictions.sh

=== Simple Project Directory Protection - Revert ===
Project root: /home/user/simple

Restoring original permissions from: scripts/privilege/.permissions_backup

Restoring: . (775) owner=user:user
  ✓ Restored
Restoring: doc (775) owner=user:user
  ✓ Restored
Restoring: examples (775) owner=user:user
  ✓ Restored
Restoring: scripts (775) owner=user:user
  ✓ Restored

=== Restrictions Reverted Successfully ===
```

### Windows Examples

#### Apply restrictions
```batch
C:\simple> Right-click scripts\privilege\apply_restrictions.bat -> "Run as administrator"

=== Simple Project Directory Protection (Windows) ===
Project root: C:\simple

Applying restrictions to prevent file creation/deletion in:
  - Project root (.)
  - doc\
  - examples\
  - scripts\

Saving current permissions...
Backup saved to: scripts\privilege\.permissions_backup.txt

Applying restrictions...
Applying to project root...
  ✓ Project root: removed write permission
Applying to doc\...
  ✓ doc\: removed write permission
Applying to examples\...
  ✓ examples\: removed write permission
Applying to scripts\...
  ✓ scripts\: removed write permission

=== Restrictions Applied Successfully ===

Permissions denied:
  - WD  = Write Data (create files)
  - AD  = Append Data (create folders)
  - WEA = Write Extended Attributes
  - WA  = Write Attributes
```

#### Test restrictions
```batch
REM This will FAIL (good!)
C:\simple> echo test > doc\newfile.txt
Access is denied.

REM This will SUCCEED (subdirectories are writable)
C:\simple> echo test > doc\guide\newfile.txt
[OK]

REM This will SUCCEED (existing files are modifiable)
C:\simple> echo test >> doc\README.md
[OK]
```

#### Revert restrictions
```batch
C:\simple> Right-click scripts\privilege\revert_restrictions.bat -> "Run as administrator"

=== Simple Project Directory Protection - Revert (Windows) ===
Project root: C:\simple

Removing deny rules...
Removing restrictions from project root...
  ✓ Project root: removed deny rule
Removing restrictions from doc\...
  ✓ doc\: removed deny rule
Removing restrictions from examples\...
  ✓ examples\: removed deny rule
Removing restrictions from scripts\...
  ✓ scripts\: removed deny rule

Restoring original ACLs...
Restoring project root ACLs...
  ✓ Project root restored
Restoring doc\ ACLs...
  ✓ doc\ restored
Restoring examples\ ACLs...
  ✓ examples\ restored
Restoring scripts\ ACLs...
  ✓ scripts\ restored

=== Restrictions Reverted Successfully ===
```

## Use Cases

1. **Development protection**: Prevent accidentally creating files in root directories during development
2. **CI/CD safety**: Apply restrictions in CI environments to catch improper file placements
3. **Team collaboration**: Enforce directory structure discipline in shared repositories
4. **Cleanup workflows**: Apply temporarily while running cleanup scripts

## Technical Details

### How it works

**Directory write permission** controls:
- ✅ Creating new files/directories in that directory
- ✅ Deleting files/directories from that directory
- ✅ Renaming files/directories in that directory

**File permissions** control:
- ✅ Reading file contents
- ✅ Modifying file contents
- ✅ Executing files

By removing write permission from a directory (but not its files or subdirectories), we prevent creating/deleting at that level while preserving all other operations.

### Permission format

Permissions are saved in format: `path mode owner group`

Example:
```
. 775 ormastes ormastes
doc 775 ormastes ormastes
```

### Backup location

Permissions backup: `scripts/privilege/.permissions_backup`

This file is created by `apply_restrictions.sh` and removed by `revert_restrictions.sh`.

## Requirements

### Unix/Linux/macOS/FreeBSD
- **Operating System**: Linux, macOS, or FreeBSD
- **Commands**: Standard `chmod`, `chown`, `stat` (automatically detects GNU vs BSD)
- **Permissions**: sudo/root access to modify directory permissions
- **Shell**: Bash

### Windows
- **Operating System**: Windows 7 or later with NTFS filesystem
- **Commands**: `icacls` (built-in), `net` (for admin check)
- **Permissions**: Administrator access
- **Shell**: Command Prompt (cmd.exe) or PowerShell

### Cross-Platform Compatibility

✅ **Linux** - Uses GNU stat (`stat -c`) + chmod
✅ **macOS** - Uses BSD stat (`stat -f`) + chmod
✅ **FreeBSD** - Uses BSD stat (`stat -f`) + chmod
✅ **Windows** - Uses icacls for NTFS ACL management

Shell scripts automatically detect your OS and use the appropriate command syntax.

## Warnings

⚠️ **Root/Admin access required**:
- Unix/Linux/macOS: Scripts must be run with `sudo`
- Windows: Scripts must be run as Administrator (right-click -> "Run as administrator")

⚠️ **Backup important**: Do not delete backup files while restrictions are active:
- Unix/Linux/macOS: `.permissions_backup`
- Windows: `.permissions_backup.txt` and `.permissions_backup.*.{dir}` files

⚠️ **Git tracking**: All backup files are gitignored. Restrictions must be reapplied after each checkout.

⚠️ **Windows NTFS only**: Windows scripts require NTFS filesystem. FAT32/exFAT filesystems do not support ACLs.

## Integration with Development Workflow

### Option 1: Manual (recommended)
Apply restrictions when needed:
```bash
sudo ./scripts/privilege/apply_restrictions.sh
# ... do work ...
sudo ./scripts/privilege/revert_restrictions.sh
```

### Option 2: Git hooks (advanced)
Add to `.git/hooks/post-checkout`:
```bash
#!/bin/bash
sudo ./scripts/privilege/apply_restrictions.sh
```

### Option 3: CI/CD
Apply in CI pipeline before running tests:
```yaml
- name: Apply directory restrictions
  run: sudo ./scripts/privilege/apply_restrictions.sh
```

## Troubleshooting

**Error: "This script must be run with sudo"**
- Run with `sudo` prefix

**Error: "No backup file found"**
- Restrictions were never applied, or backup was deleted
- Safe to ignore if trying to revert non-existent restrictions

**Error: "Restrictions already applied"**
- Run `revert_restrictions.sh` first, then apply again

**Warning: "Failed to restore permissions/ownership"**
- Usually harmless, indicates directory no longer exists or permission issue
- Script continues with other directories

## Files

```
scripts/privilege/
├── apply_restrictions.sh      # Unix/Linux/macOS: Apply write restrictions
├── revert_restrictions.sh     # Unix/Linux/macOS: Revert to original permissions
├── apply_restrictions.bat     # Windows: Apply write restrictions
├── revert_restrictions.bat    # Windows: Revert to original permissions
├── README.md                  # This file
├── .gitignore                 # Excludes backup files from git
├── .permissions_backup        # Unix backup (auto-created/removed)
└── .permissions_backup.*      # Windows backups (auto-created/removed)
```

## See Also

### Unix/Linux/macOS
- `man chmod` - Change file mode bits
- `man chown` - Change file owner and group
- `man stat` - Display file or filesystem status

### Windows
- `icacls /?` - Display or modify ACLs (Access Control Lists)
- `cacls /?` - Display or modify ACLs (deprecated, but simpler)
- [NTFS Permissions Documentation](https://docs.microsoft.com/en-us/windows-server/storage/file-server/ntfs-overview)
