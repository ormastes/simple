use std::fs;

use assert_cmd::Command;
use tempfile::tempdir;

fn read_u64(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

#[test]
fn compile_driver_mode_dynamic_writes_lsmf_with_smf_and_drv_manifest() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("net_card.spl");
    let output = dir.path().join("net_card.lsm");

    fs::write(
        &source,
        r#"@driver(class = 2, vendor = 0x1B36, device = [0x000E], version = "1.0")
fn driver_init():
    return 0
"#,
    )
    .expect("write source");

    let mut cmd = Command::cargo_bin("simple").expect("simple binary");
    let assert = cmd
        .arg("compile")
        .arg("--driver-mode=dynamic")
        .arg(&source)
        .arg("-o")
        .arg(&output)
        .assert();
    assert.success();

    let archive = fs::read(&output).expect("read lsm");
    assert_eq!(&archive[..4], b"LSMF");
    assert_eq!(u32::from_le_bytes(archive[8..12].try_into().unwrap()), 1);

    let smf_offset = read_u64(&archive, 128 + 64);
    let smf_size = read_u64(&archive, 128 + 72);
    let smf = &archive[smf_offset as usize..(smf_offset + smf_size) as usize];
    assert_eq!(&smf[..4], b"SMF\0");
    assert!(smf.windows(b".drv_manifest".len()).any(|w| w == b".drv_manifest"));
    assert!(smf.windows(4).any(|w| w == b"SVRD"));
}

#[test]
fn compile_driver_mode_space_form_does_not_treat_dynamic_as_source() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("plain.spl");
    let output = dir.path().join("plain.lsm");
    fs::write(&source, "fn main():\n    return 0\n").expect("write source");

    let mut cmd = Command::cargo_bin("simple").expect("simple binary");
    cmd.arg("compile")
        .arg("--driver-mode")
        .arg("dynamic")
        .arg(&source)
        .arg("-o")
        .arg(&output)
        .assert()
        .success();

    let archive = fs::read(&output).expect("read lsm");
    assert_eq!(&archive[..4], b"LSMF");
}
