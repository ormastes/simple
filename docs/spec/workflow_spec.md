# Load and update config

*Source: `./vulkan-backend/simple/std_lib/test/system/sdn/workflow_spec.spl`*

---

let path = create_test_file(config)

            # Load and update config
            match SdnDocument.from_file(path):
                case Ok(mut doc):
                    # Update version
                    doc.set("app.version", SdnValue.String("1.1.0"))

                    # Enable debug mode
                    doc.set("app.debug", SdnValue.Bool(True))

                    # Change server port
                    doc.set("server.port", SdnValue.Int(9000))

                    # Add new database setting
                    doc.set("database.pool_size", SdnValue.Int(20))

                    # Save
                    match doc.write_file(path):
                        case Ok(_):
                            pass
                        case Err(e):
                            fail("Failed to save config: ${e}")
                case Err(e):
                    fail("Failed to load config: ${e}")

            # Verify changes
            match SdnDocument.from_file(path):
                case Ok(doc):
                    expect doc.get("app.version").flatmap(|v| v.as_str()) == Some("1.1.0")
                    expect doc.get("app.debug").flatmap(|v| v.as_bool()) == Some(True)
                    expect doc.get("server.port").flatmap(|v| v.as_i64()) == Some(9000)
                    expect doc.get("database.pool_size").flatmap(|v| v.as_i64()) == Some(20)
                case Err(e):
                    fail("Failed to verify config: ${e}")

            cleanup_file(path)

        it "manages multiple config files":
            # Create dev config
            let dev_config = "env: development\nport: 8080\ndebug: true"
            let dev_path = create_test_file(dev_config)

            # Create prod config
            let prod_config = "env: production\nport: 80\ndebug: false"
            let prod_path = create_test_file(prod_config)

            # Load both
            let dev_doc = SdnDocument.from_file(dev_path)
            let prod_doc = SdnDocument.from_file(prod_path)

            match (dev_doc, prod_doc):
                case (Ok(dev), Ok(prod)):
                    # Verify dev config
                    expect dev.get("env").flatmap(|v| v.as_str()) == Some("development")
                    expect dev.get("debug").flatmap(|v| v.as_bool()) == Some(True)

                    # Verify prod config
                    expect prod.get("env").flatmap(|v| v.as_str()) == Some("production")
                    expect prod.get("debug").flatmap(|v| v.as_bool()) == Some(False)
                case _:
                    fail("Failed to load configs")

            cleanup_file(dev_path)
            cleanup_file(prod_path)

    context "data migration":
        it "migrates JSON config to SDN":
            # Create JSON config
            let json_config = """
{
  "app": {
    "name": "MyApp",
    "version": "2.0.0"
  },
  "features": ["auth", "logging", "metrics"]
}

let sdn_path = create_test_file(sdn_data)

            # Load and convert to JSON
            match SdnDocument.from_file(sdn_path):
                case Ok(doc):
                    let json_content = doc.to_json()

                    # Save as JSON
                    let json_path = "${sdn_path}.json"
                    match fs.write(json_path, json_content):
                        case Ok(_):
                            # Verify JSON is valid
                            match fs.read_to_string(json_path):
                                case Ok(content):
                                    match json.parse(content):
                                        case Ok(_):
                                            pass  # Valid JSON
                                        case Err(e):
                                            fail("Invalid JSON output: ${e}")
                                case Err(e):
                                    fail("Failed to read JSON: ${e}")

                            cleanup_file(json_path)
                        case Err(e):
                            fail("Failed to write JSON: ${e}")
                case Err(e):
                    fail("Failed to load SDN: ${e}")

            cleanup_file(sdn_path)

    context "batch operations":
        it "updates multiple values in batch":
            let config = """
service_a:
    port: 8001
    enabled: true

service_b:
    port: 8002
    enabled: true

service_c:
    port: 8003
    enabled: true
