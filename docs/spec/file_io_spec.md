# file_io_spec

*Source: `./vulkan-backend/simple/std_lib/test/system/sdn/file_io_spec.spl`*

---

let path = create_test_file(content)

            match SdnDocument.from_file(path):
                case Ok(doc):
                    expect doc.get("server.host").flatmap(|v| v.as_str()) == Some("localhost")
                    expect doc.get("server.port").flatmap(|v| v.as_i64()) == Some(8080)
                    expect doc.get("server.config.debug").flatmap(|v| v.as_bool()) == Some(True)
                    expect doc.get("server.config.workers").flatmap(|v| v.as_i64()) == Some(4)
                case Err(e):
                    fail("Failed to load file: ${e}")

            cleanup_file(path)

        it "loads arrays and dicts from file":
            let content = """
items = [1, 2, 3, 4, 5]
config = {x: 10, y: 20, z: 30}
nested:
    data = [a, b, c]
