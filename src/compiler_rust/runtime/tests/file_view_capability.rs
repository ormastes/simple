use simple_runtime as _;

#[cfg(unix)]
mod unix {
    use std::os::unix::fs::symlink;

    unsafe extern "C" {
        fn rt_string_new(bytes: *const u8, length: u64) -> i64;
        fn rt_array_len_safe(value: i64) -> i64;
        fn rt_array_get(array: *mut std::ffi::c_void, index: i64) -> i64;
        fn rt_file_view_open_beneath_no_follow_v1(root: i64, path: i64) -> i64;
        fn rt_file_view_pread_exact_v1(descriptor: i64, offset: u64, length: u64) -> i64;
        fn rt_file_view_map_copy_v1(descriptor: i64, offset: u64, length: u64) -> i64;
        fn rt_file_view_device_v1(descriptor: i64) -> i64;
        fn rt_file_view_inode_v1(descriptor: i64) -> i64;
        fn rt_file_view_size_v1(descriptor: i64) -> i64;
        fn rt_file_view_mapping_supported_v1(descriptor: i64) -> i8;
        fn rt_file_view_prefetch_v1(descriptor: i64, offset: u64, length: u64) -> i8;
        fn rt_file_view_close_v1(descriptor: i64) -> i8;
        fn rt_pinned_archive_open_beneath_v1(root: i64, path: i64) -> i64;
        fn rt_pinned_archive_close_v1(descriptor: i64) -> i8;
    }

    unsafe fn text(value: &str) -> i64 {
        unsafe { rt_string_new(value.as_ptr(), value.len() as u64) }
    }

    unsafe fn bytes(value: i64) -> Vec<u8> {
        let length = unsafe { rt_array_len_safe(value) };
        assert!(length >= 0);
        (0..length)
            .map(|index| unsafe {
                (rt_array_get(value as *mut std::ffi::c_void, index) >> 3) as u8
            })
            .collect()
    }

    #[test]
    fn pinned_view_reads_one_verified_descriptor_and_rejects_escape_or_symlink() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("root");
        let nested = root.join("cas/sha256/ab");
        std::fs::create_dir_all(&nested).unwrap();
        let archive = nested.join("payload.bin");
        std::fs::write(&archive, b"0123456789").unwrap();
        let outside = temp.path().join("outside.bin");
        std::fs::write(&outside, b"outside").unwrap();
        symlink(&outside, nested.join("link.bin")).unwrap();

        unsafe {
            let root_value = text(root.to_str().unwrap());
            let archive_value = text(archive.to_str().unwrap());
            let descriptor = rt_file_view_open_beneath_no_follow_v1(root_value, archive_value);
            assert!(descriptor >= 0);
            assert!(rt_file_view_device_v1(descriptor) >= 0);
            assert!(rt_file_view_inode_v1(descriptor) >= 0);
            assert_eq!(rt_file_view_size_v1(descriptor), 10);
            assert_eq!(bytes(rt_file_view_pread_exact_v1(descriptor, 2, 4)), b"2345");
            assert_eq!(bytes(rt_file_view_map_copy_v1(descriptor, 4, 3)), b"456");
            assert_eq!(rt_file_view_close_v1(descriptor), 1);

            let relative = text("cas/sha256/ab/payload.bin");
            let pinned = rt_pinned_archive_open_beneath_v1(root_value, relative);
            assert!(pinned >= 0);
            assert_eq!(rt_pinned_archive_close_v1(pinned), 1);

            let escape = text("../outside.bin");
            assert_eq!(rt_file_view_open_beneath_no_follow_v1(root_value, escape), -2);
            let link = text("cas/sha256/ab/link.bin");
            assert_eq!(rt_file_view_open_beneath_no_follow_v1(root_value, link), -3);
            let outside_value = text(outside.to_str().unwrap());
            assert_eq!(rt_file_view_open_beneath_no_follow_v1(root_value, outside_value), -2);
        }
    }

    #[test]
    fn view_rejects_a_symlink_root_with_a_trailing_separator() {
        let temp = tempfile::tempdir().unwrap();
        let real_root = temp.path().join("real");
        std::fs::create_dir(&real_root).unwrap();
        std::fs::write(real_root.join("payload"), b"data").unwrap();
        let link_root = temp.path().join("linked");
        symlink(&real_root, &link_root).unwrap();
        unsafe {
            let descriptor = rt_file_view_open_beneath_no_follow_v1(
                text(&format!("{}/", link_root.display())), text("payload"));
            if descriptor >= 0 {
                rt_file_view_close_v1(descriptor);
            }
            assert!(descriptor < 0, "a trailing slash must not bypass root O_NOFOLLOW");
        }
    }

    #[test]
    fn view_bounds_fail_with_nil_and_path_replacement_keeps_the_open_inode() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("payload");
        std::fs::write(&path, [0, 127, 128, 255]).unwrap();
        symlink(temp.path(), temp.path().join("child_link")).unwrap();
        unsafe {
            let root = text(temp.path().to_str().unwrap());
            let descriptor = rt_file_view_open_beneath_no_follow_v1(root, text("payload"));
            assert!(descriptor >= 0);
            assert_eq!(rt_file_view_mapping_supported_v1(descriptor), 1);
            assert_eq!(bytes(rt_file_view_pread_exact_v1(descriptor, 0, 4)), [0, 127, 128, 255]);
            assert_eq!(bytes(rt_file_view_map_copy_v1(descriptor, 0, 4)), [0, 127, 128, 255]);
            assert!(bytes(rt_file_view_pread_exact_v1(descriptor, 4, 0)).is_empty());
            assert!(bytes(rt_file_view_map_copy_v1(descriptor, 4, 0)).is_empty());
            for (offset, length) in [(4, 1), (5, 0), (u64::MAX, 1), (0, u64::MAX)] {
                assert_eq!(rt_file_view_pread_exact_v1(descriptor, offset, length), 3);
                assert_eq!(rt_file_view_map_copy_v1(descriptor, offset, length), 3);
                assert_eq!(rt_file_view_prefetch_v1(descriptor, offset, length), 0);
            }
            assert_eq!(rt_file_view_open_beneath_no_follow_v1(root, text("child_link/payload")), -3);
            assert_eq!(rt_file_view_open_beneath_no_follow_v1(root, text("payload\0ignored")), -2);
            assert_eq!(rt_file_view_open_beneath_no_follow_v1(
                text(&format!("{}\0ignored", temp.path().display())), text("payload")), -2);

            let inode = rt_file_view_inode_v1(descriptor);
            std::fs::rename(&path, temp.path().join("old-payload")).unwrap();
            std::fs::write(&path, b"replacement").unwrap();
            assert_eq!(rt_file_view_inode_v1(descriptor), inode);
            assert_eq!(rt_file_view_size_v1(descriptor), 4);
            assert_eq!(bytes(rt_file_view_pread_exact_v1(descriptor, 0, 4)), [0, 127, 128, 255]);
            assert_eq!(rt_file_view_close_v1(descriptor), 1);
            assert_eq!(rt_file_view_pread_exact_v1(-1, 0, 0), 3);
            assert_eq!(rt_file_view_map_copy_v1(-1, 0, 0), 3);
            assert_eq!(rt_file_view_mapping_supported_v1(-1), 0);
            assert_eq!(rt_file_view_inode_v1(-1), -1);
            assert_eq!(rt_file_view_close_v1(-1), 0);
        }
    }
}
