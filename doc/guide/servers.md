# Server Access Information

## FreeBSD (OPNsense Router)

| Property | Value |
|----------|-------|
| **Host** | `192.168.1.1` |
| **SSH Port** | `2202` |
| **User** | `root` |
| **Password** | `yic1323` |
| **OS** | FreeBSD (OPNsense) |
| **Arch** | x86_64 (amd64) |

### Quick Access

```bash
# SSH into FreeBSD
ssh -p 2202 root@192.168.1.1

# SCP file to FreeBSD
scp -P 2202 <local-file> root@192.168.1.1:<remote-path>

# SCP with password (non-interactive)
sshpass -p "yic1323" ssh -p 2202 root@192.168.1.1
sshpass -p "yic1323" scp -P 2202 <local-file> root@192.168.1.1:<remote-path>
```

### Testing Simple Compiler on FreeBSD

```bash
# 1. Cross-compile for FreeBSD (from Linux)
cd src/compiler_rust
cargo build --profile bootstrap -p simple-driver --target x86_64-unknown-freebsd

# 2. Copy binary to FreeBSD
sshpass -p "yic1323" scp -P 2202 \
  target/x86_64-unknown-freebsd/bootstrap/simple \
  root@192.168.1.1:/usr/local/bin/simple

# 3. Copy test files
sshpass -p "yic1323" scp -r -P 2202 \
  ../../test/ root@192.168.1.1:/tmp/simple-test/

# 4. Run smoke test
sshpass -p "yic1323" ssh -p 2202 root@192.168.1.1 \
  '/usr/local/bin/simple --version'

# 5. Run full test suite
sshpass -p "yic1323" ssh -p 2202 root@192.168.1.1 \
  'cd /tmp/simple-test && /usr/local/bin/simple test'
```

### Notes

- OPNsense is a FreeBSD-based firewall/router distribution
- The SSH port is non-standard (2202 instead of 22)
- Binary must be cross-compiled as `x86_64-unknown-freebsd` ELF
- Use `sshpass` for scripted/non-interactive access
