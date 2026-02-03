//! archive module
//!
//! Archive and Compression FFI
//! 
//! Tar archives, gzip, and xz compression.

use std::ffi::CStr;
use std::os::raw::c_char;
use std::fs::File;
use std::io::{Read, Write};
use tar::Archive;
use flate2::read::GzDecoder;
use flate2::write::GzEncoder;
use flate2::Compression;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Extract tar archive to directory
#[no_mangle]
pub unsafe extern "C" fn rt_tar_extract(tar_path: *const c_char, dest_dir: *const c_char) -> bool {
    let tar_str = CStr::from_ptr(tar_path as *const i8).to_string_lossy();
    let dest_str = CStr::from_ptr(dest_dir as *const i8).to_string_lossy();
    match File::open(tar_str.as_ref()) {
        Ok(file) => {
            let mut archive = Archive::new(file);
            archive.unpack(dest_str.as_ref()).is_ok()
        }
        Err(_) => false,
    }
}

/// Create tar archive from directory (not yet implemented)
#[no_mangle]
pub unsafe extern "C" fn rt_tar_create(tar_path: *const c_char, _src_dir: *const c_char) -> bool {
    // TODO: Implement tar creation
    let _tar_str = CStr::from_ptr(tar_path as *const i8).to_string_lossy();
    false
}

/// Compress file with gzip
#[no_mangle]
pub unsafe extern "C" fn rt_gzip_compress(input_path: *const c_char, output_path: *const c_char) -> bool {
    let in_str = CStr::from_ptr(input_path as *const i8).to_string_lossy();
    let out_str = CStr::from_ptr(output_path as *const i8).to_string_lossy();
    match (File::open(in_str.as_ref()), File::create(out_str.as_ref())) {
        (Ok(mut input), Ok(output)) => {
            let mut encoder = GzEncoder::new(output, Compression::default());
            let mut buffer = Vec::new();
            if input.read_to_end(&mut buffer).is_err() {
                return false;
            }
            encoder.write_all(&buffer).is_ok() && encoder.finish().is_ok()
        }
        _ => false,
    }
}

/// Decompress gzip file
#[no_mangle]
pub unsafe extern "C" fn rt_gzip_decompress(input_path: *const c_char, output_path: *const c_char) -> bool {
    let in_str = CStr::from_ptr(input_path as *const i8).to_string_lossy();
    let out_str = CStr::from_ptr(output_path as *const i8).to_string_lossy();
    match (File::open(in_str.as_ref()), File::create(out_str.as_ref())) {
        (Ok(input), Ok(mut output)) => {
            let mut decoder = GzDecoder::new(input);
            let mut buffer = Vec::new();
            if decoder.read_to_end(&mut buffer).is_err() {
                return false;
            }
            output.write_all(&buffer).is_ok()
        }
        _ => false,
    }
}

