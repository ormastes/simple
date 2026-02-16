# Resource Limit Scripts

Control memory, CPU, and process limits for commands and tmux sessions.

## Automatic tmux Limits (Recommended)

**Make every tmux session automatically limited to 32GB/16 processes:**

```bash
# Install (one-time setup)
./scripts/resource/install_tmux_limits.sh

# Restart shell or:
source ~/.bashrc  # or ~/.zshrc

# Now tmux always starts with limits!
tmux              # Automatically limited to 32GB, 16 processes
tmux attach       # Attaching doesn't add new limits
```

**Customize defaults:**
```bash
# Install with different defaults
./scripts/resource/install_tmux_limits.sh 64G 32

# Or change after install
export TMUX_MEMORY_LIMIT=64G
export TMUX_PROCESS_LIMIT=32
tmux
```

**Uninstall:**
```bash
./scripts/resource/uninstall_tmux_limits.sh
```

## Quick Start

### Run command with defaults (32GB RAM, 16 processes)
```bash
./scripts/resource/run_limited.sh -- your-command
```

### Start tmux with defaults
```bash
./scripts/resource/tmux_limited.sh
```

### Custom limits
```bash
./scripts/resource/run_limited.sh -m 8G -p 4 -- python train.py
```

## Default Limits

| Resource | Default Value |
|----------|--------------|
| **Memory** | 32GB |
| **Processes** | 16 |
| **CPU** | 100% (1 core) |
| **Nice** | 0 (normal priority) |
| **File Descriptors** | 65,536 |

## Scripts

### `run_limited.sh`
Run any command with resource limits.

**Syntax:**
```bash
./run_limited.sh [options] -- command [args...]
```

**Options:**
- `-m, --memory SIZE` - Memory limit (default: 32G)
  - Examples: `1G`, `512M`, `32G`, `64G`
- `-p, --processes NUM` - Max processes (default: 16)
- `-c, --cpu PERCENT` - CPU usage % (default: 100)
- `-n, --nice LEVEL` - Priority -20 to 19 (default: 0)
- `-f, --fds NUM` - File descriptors (default: 65536)
- `--systemd` - Force systemd-run (best method)
- `--prlimit` - Force prlimit
- `-v, --verbose` - Show details

**Examples:**
```bash
# Default limits
./run_limited.sh -- python script.py

# Custom memory and processes
./run_limited.sh -m 8G -p 4 -- ./compile.sh

# High memory task
./run_limited.sh -m 64G -p 32 -- data-processor

# Low priority background job
./run_limited.sh -n 10 -m 4G -- backup.sh

# Limit CPU to 50% of one core
./run_limited.sh -c 50 -- intensive-task
```

### `tmux_limited.sh`
Start tmux session where all panes inherit resource limits.

**Syntax:**
```bash
./tmux_limited.sh [session-name] [options]
```

**Options:**
- `-m, --memory SIZE` - Memory limit (default: 32G)
- `-p, --processes NUM` - Max processes (default: 16)
- `-c, --cpu PERCENT` - CPU usage % (default: 100)
- `-n, --nice LEVEL` - Priority (default: 0)

**Examples:**
```bash
# Default session (32GB, 16 processes)
./tmux_limited.sh

# Named session with defaults
./tmux_limited.sh mywork

# Development session (8GB, 8 processes)
./tmux_limited.sh dev -m 8G -p 8

# ML training session (64GB, 32 processes)
./tmux_limited.sh training -m 64G -p 32

# Background work (low priority)
./tmux_limited.sh background -m 4G -p 4 -n 10
```

**Inside tmux:**
- All new panes inherit limits automatically
- `Ctrl-b c` - Create new pane (with limits)
- `Ctrl-b d` - Detach
- `tmux attach -t <name>` - Reattach

**Check active limits:**
```bash
# Inside tmux
ulimit -a                  # See all limits
cat /proc/self/limits      # Detailed (Linux)
```

### `limits.conf`
Preset configurations for different workloads.

**Usage:**
```bash
source scripts/resource/limits.conf
./run_limited.sh -m $DEV_MEMORY -p $DEV_PROCESSES -- command
```

**Presets:**

| Preset | Memory | Processes | Use Case |
|--------|--------|-----------|----------|
| `DEFAULT` | 32GB | 16 | General purpose |
| `LIGHT` | 4GB | 4 | Small tasks |
| `MEDIUM` | 16GB | 8 | Medium workloads |
| `HEAVY` | 64GB | 32 | Heavy processing |
| `DEV` | 8GB | 8 | Development |
| `BUILD` | 16GB | 16 | CI/CD builds |
| `TEST` | 4GB | 4 | Test isolation |
| `ML` | 128GB | 64 | ML training |
| `BACKGROUND` | 2GB | 2 | Background jobs |

**Example with presets:**
```bash
source scripts/resource/limits.conf

# Use test preset
./run_limited.sh -m $TEST_MEMORY -p $TEST_PROCESSES -- pytest

# Use ML preset
./tmux_limited.sh training -m $ML_MEMORY -p $ML_PROCESSES
```

## How It Works

### Three Methods (Auto-Detected)

1. **systemd-run** (Preferred on Linux with systemd)
   - Uses cgroups v2 for accurate limits
   - Memory, CPU%, and process limits
   - Most reliable method

2. **prlimit** (Fallback)
   - Per-process limits
   - Works without systemd
   - Good accuracy

3. **ulimit** (Universal fallback)
   - Built-in shell limits
   - Works everywhere
   - Basic functionality (no CPU% limiting)

### Auto-Detection
Scripts automatically choose the best available method:
- Linux with systemd → `systemd-run`
- Linux without systemd → `prlimit` or `ulimit`
- macOS/FreeBSD → `ulimit`

## Use Cases

### 1. Prevent OOM (Out of Memory)
```bash
# Limit memory-hungry process
./run_limited.sh -m 16G -- memory-intensive-app
```

### 2. Control Fork Bombs
```bash
# Prevent runaway process creation
./run_limited.sh -p 4 -- untrusted-script
```

### 3. Fair Resource Sharing
```bash
# Multiple users on shared server
./tmux_limited.sh user1 -m 8G -p 4
./tmux_limited.sh user2 -m 8G -p 4
```

### 4. CI/CD Testing
```bash
# Reproducible test environment
./run_limited.sh -m 4G -p 4 -- pytest tests/
```

### 5. Background Processing
```bash
# Low priority batch job
./run_limited.sh -n 15 -m 2G -- batch-process.sh
```

### 6. Development Isolation
```bash
# Limit dev environment
./tmux_limited.sh dev -m 8G -p 8
```

## Real-World Examples

### Compile Project
```bash
# Limit compiler to 16GB, 8 cores
./run_limited.sh -m 16G -p 8 -- make -j8
```

### Train ML Model
```bash
# Start tmux with 64GB for training
./tmux_limited.sh ml -m 64G -p 16
# Inside tmux:
python train.py --epochs 100
```

### Run Tests in Isolation
```bash
# Conservative limits for tests
./run_limited.sh -m 4G -p 4 -- cargo test
```

### Database Operations
```bash
# Limit memory for large query
./run_limited.sh -m 32G -- psql -f heavy_query.sql
```

### Video Encoding
```bash
# Limit ffmpeg memory
./run_limited.sh -m 8G -p 4 -- ffmpeg -i input.mp4 output.mp4
```

## Monitoring Limits

### Check Current Limits
```bash
# Soft and hard limits
ulimit -a

# Detailed limits (Linux)
cat /proc/self/limits

# Memory usage
free -h

# Process count
ps aux | wc -l
```

### Watch Resource Usage
```bash
# Real-time monitoring
htop

# Memory usage
watch -n 1 free -h

# Processes
watch -n 1 "ps aux | grep your-process"
```

## Platform Support

| Platform | systemd-run | prlimit | ulimit | Status |
|----------|-------------|---------|--------|--------|
| Linux (systemd) | ✅ | ✅ | ✅ | Full support |
| Linux (non-systemd) | ❌ | ✅ | ✅ | Good support |
| macOS | ❌ | ❌ | ✅ | Basic support |
| FreeBSD | ❌ | ❌ | ✅ | Basic support |

**Note:** CPU% limiting requires systemd-run. Other platforms can limit memory and processes but not CPU percentage.

## Troubleshooting

### "systemd-run not found"
Script will automatically fall back to prlimit or ulimit.

### "Operation not permitted"
Some limits require root/sudo:
```bash
# If needed, prefix with sudo
sudo ./run_limited.sh -m 32G -- command
```

### Limits Not Applied
Check if limit is too high:
```bash
# Check system limits
cat /proc/sys/vm/max_map_count
sysctl -a | grep kernel.pid_max
```

### CPU Limiting Not Working
CPU% limiting requires systemd:
```bash
# Check if systemd is available
systemctl --version

# Force systemd method
./run_limited.sh --systemd -c 50 -- command
```

### Memory Limit Too Low
Process crashes with "cannot allocate memory":
```bash
# Increase memory limit
./run_limited.sh -m 64G -- command
```

## Advanced Usage

### Nested Limits
```bash
# Outer limit: 32GB for tmux session
./tmux_limited.sh work -m 32G -p 16

# Inside tmux, further limit individual commands
./run_limited.sh -m 8G -p 4 -- heavy-task
```

### Combining with Other Tools
```bash
# With nice
nice -n 10 ./run_limited.sh -m 16G -- command

# With ionice (I/O priority)
ionice -c 3 ./run_limited.sh -m 16G -- io-heavy-task

# With taskset (CPU affinity)
taskset -c 0-3 ./run_limited.sh -m 16G -- command
```

### Shell Alias
Add to `~/.bashrc`:
```bash
alias limited='~/simple/scripts/resource/run_limited.sh'
alias tlimited='~/simple/scripts/resource/tmux_limited.sh'

# Use as:
limited -- python script.py
tlimited mywork -m 8G
```

## Files

```
scripts/resource/
├── run_limited.sh       # Command wrapper with limits
├── tmux_limited.sh      # tmux session launcher
├── limits.conf          # Preset configurations
└── README.md            # This file
```

## See Also

- `man ulimit` - Shell resource limits
- `man prlimit` - Get/set process resource limits
- `man systemd-run` - Run programs in transient scope units
- `man nice` - Run program with modified scheduling priority
- `man cgroups` - Linux Control Groups

## Automatic tmux Limits (Details)

### What Gets Installed

The install script adds to your `~/.bashrc` or `~/.zshrc`:

```bash
export TMUX_MEMORY_LIMIT="32G"
export TMUX_PROCESS_LIMIT="16"
export TMUX_LIMITS_ENABLED="1"
alias tmux="/path/to/tmux-wrapper.sh"
```

### How It Works

1. **Smart Detection**: Wrapper detects if you're creating a new session or attaching
2. **New Sessions**: Applies limits automatically (tmux, tmux new, etc.)
3. **Attaching**: No limits applied (tmux attach, tmux a)
4. **Environment Control**: Change limits via environment variables

### Control Limits

```bash
# Use custom limits for one session
TMUX_MEMORY_LIMIT=64G TMUX_PROCESS_LIMIT=32 tmux

# Disable limits for one session
TMUX_LIMITS_ENABLED=0 tmux

# Change defaults permanently
# Edit ~/.bashrc and change TMUX_MEMORY_LIMIT
```

### Verify It's Working

```bash
# Start tmux
tmux

# Inside tmux, check limits
ulimit -a
# Look for:
# max memory size (kbytes, -m): 33554432  (32GB)
# max user processes (-u): 16

# Or more detailed
cat /proc/self/limits
```

