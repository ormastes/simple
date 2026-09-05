# FAT32 Mount Value Owner Contract

Source: `test/01_unit/os/kernel/fs/fat32_mount_value_owner_contract_test.shs`

Evidence class: `source-contract`.

The shell check verifies that mount state remains owned by the boot publication
path and that FAT32 mounting uses the canonical filesystem value. It performs
static source checks only; it does not mount media or boot a guest.

