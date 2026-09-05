# Canonical Windows SOSIX guest descriptors. Dot-sourced by the matrix peer.
function Get-RowDescriptors([string]$RepoRoot) {
    $build = Join-Path $RepoRoot 'build/os'
    $spec = Join-Path $RepoRoot 'test/03_system/os/qemu'
    return @(
        [pscustomobject]@{
            Guest='x86_32'; QemuKey='simple_qemu_x86_32_bin'
            Kernel=(Join-Path $build 'simpleos_x86_32_initrd_fs_exec_probe.elf')
            Image=(Join-Path $build 'fat32-x86_32.img')
            ImageArg='build/os/fat32-x86_32.img'
            Spec=(Join-Path $spec 'sys_qemu_x86_32_fs_exec_spec.spl')
            Args=@('-machine','pc','-cpu','qemu32,+pae,+nx','-m','128M','-nographic','-initrd','build/os/fat32-x86_32.img','-device','isa-debug-exit,iobase=0xf4,iosize=0x04','-kernel','build/os/simpleos_x86_32_initrd_fs_exec_probe.elf')
            ExactReap='X86_32_EXACT_REAP generation=2 stale_rejected=true pending_overwrite_rejected=true status=-13'
            CollectorNonceEcho=$true; RunContractReady=$false
            FirmwareMode='direct-kernel'; FirmwareStages='guest-entry'
        },
        [pscustomobject]@{
            Guest='x86_64'; QemuKey='simple_qemu_x86_64_bin'
            Kernel=(Join-Path $build 'simpleos_x86_64_fs_exec.elf')
            Image=(Join-Path $build 'fat32-x86_64.img')
            ImageArg='build/os/fat32-x86_64.img'
            Spec=(Join-Path $spec 'sys_qemu_x86_64_fs_exec_spec.spl')
            Args=@('-machine','q35','-cpu','qemu64','-m','512M','-nographic','-no-reboot','-device','loader,file=build/os/simpleos_x86_64_fs_exec.elf,cpu-num=0','-device','isa-debug-exit,iobase=0xf4,iosize=0x04','-device','nvme,id=fsexec,serial=x86-64-fs-exec','-drive','file=build/os/fat32-x86_64.img,if=none,id=fsexecns1,format=raw','-device','nvme-ns,drive=fsexecns1,bus=fsexec,nsid=1')
            ExactReap='[x86_64-user] reaped pid='
            CollectorNonceEcho=$true; RunContractReady=$true
            FirmwareMode='direct-kernel'; FirmwareStages='guest-entry'
        },
        [pscustomobject]@{
            Guest='arm32'; QemuKey='simple_qemu_arm32_bin'
            Kernel=(Join-Path $build 'simpleos_arm32_fs_exec.elf')
            Image=(Join-Path $build 'fat32-arm32.img')
            ImageArg='build/os/fat32-arm32.img'
            Spec=(Join-Path $spec 'sys_qemu_arm32_fs_exec_spec.spl')
            Args=@('-machine','virt','-cpu','cortex-a15','-m','384M','-nographic','-global','virtio-mmio.force-legacy=false','-drive','file=build/os/fat32-arm32.img,if=none,id=armdisk,format=raw','-device','virtio-blk-device,drive=armdisk','-semihosting-config','enable=on,target=native','-device','loader,file=build/os/simpleos_arm32_fs_exec.elf,addr=0x40200000','-device','loader,addr=0x40200000,cpu-num=0')
            ExactReap='FS_PROGRAM_END rc=37 reaped=true generation=exact stale=denied'
            CollectorNonceEcho=$true; RunContractReady=$true
            FirmwareMode='direct-kernel'; FirmwareStages='guest-entry'
        },
        [pscustomobject]@{
            Guest='arm64'; QemuKey='simple_qemu_arm64_bin'
            Kernel=(Join-Path $build 'simpleos_arm64_fs_exec.elf')
            Image=(Join-Path $build 'fat32-arm64.img')
            ImageArg='build/os/fat32-arm64.img'
            Spec=(Join-Path $spec 'sys_qemu_arm64_fs_exec_spec.spl')
            Args=@('-machine','virt','-cpu','cortex-a72','-m','384M','-nographic','-global','virtio-mmio.force-legacy=false','-drive','file=build/os/fat32-arm64.img,if=none,id=armdisk,format=raw','-device','virtio-blk-device,drive=armdisk','-semihosting-config','enable=on,target=native','-kernel','build/os/simpleos_arm64_fs_exec.elf')
            ExactReap='[arm64-user] kernel-resumed exit=37'
            CollectorNonceEcho=$true; RunContractReady=$false
            FirmwareMode='direct-kernel'; FirmwareStages='guest-entry'
        },
        [pscustomobject]@{
            Guest='riscv32'; QemuKey='simple_qemu_riscv32_bin'
            Kernel=(Join-Path $build 'simpleos_riscv32_smf_fs.elf')
            Image=(Join-Path $build 'fat32-riscv32.img')
            ImageArg='build/os/fat32-riscv32.img'
            Spec=(Join-Path $spec 'sys_qemu_riscv32_fs_exec_spec.spl')
            Args=@('-machine','virt','-cpu','rv32','-m','256M','-nographic','-bios','none','-global','virtio-mmio.force-legacy=false','-drive','file=build/os/fat32-riscv32.img,if=none,id=rvdisk,format=raw','-device','virtio-blk-device,drive=rvdisk','-kernel','build/os/simpleos_riscv32_smf_fs.elf')
            ExactReap='FS_TASK_REAP generation='
            CollectorNonceEcho=$true; RunContractReady=$false
            FirmwareMode='direct-kernel'; FirmwareStages='guest-entry'
        },
        [pscustomobject]@{
            Guest='riscv64'; QemuKey='simple_qemu_riscv64_bin'
            Kernel=(Join-Path $build 'simpleos_riscv64_smf_fs.elf')
            Image=(Join-Path $build 'fat32-riscv64.img')
            ImageArg='build/os/fat32-riscv64.img'
            Spec=(Join-Path $spec 'sys_qemu_riscv64_fs_exec_spec.spl')
            Args=@('-machine','virt','-cpu','rv64','-m','2G','-nographic','-bios','__SOSIX_RISCV64_FIRMWARE__','-global','virtio-mmio.force-legacy=false','-drive','file=build/os/fat32-riscv64.img,if=none,id=rvdisk,format=raw','-device','virtio-blk-device,drive=rvdisk','-kernel','build/os/simpleos_riscv64_smf_fs.elf')
            ExactReap='RV64_LEGACY_FSEXEC_DISABLED reason=missing-loader-authority-token'
            CollectorNonceEcho=$true; RunContractReady=$false
            FirmwareMode='opensbi-bios'; FirmwareStages='opensbi-entry>opensbi-handoff>guest-entry'
        }
    )
}
