# roundtrip_spec

*Source: `./vulkan-backend/simple/std_lib/test/unit/sdn/roundtrip_spec.spl`*

---

match parse(original):
                case Ok(doc1):
                    let sdn = to_sdn(doc1)

                    match parse(sdn):
                        case Ok(doc2):
                            expect doc2.get_path("app.name").flatmap(|v| v.as_str()) == Some("MyService")
                            expect doc2.get_path("app.config.debug").flatmap(|v| v.as_bool()) == Some(True)
                            expect doc2.get_path("app.config.level").flatmap(|v| v.as_i64()) == Some(5)
                        case Err(e):
                            fail("Round-trip parse failed: ${e.to_string()}")
                case Err(e):
                    fail("Initial parse failed: ${e.to_string()}")

        it "preserves real config files":
            let original = """
app:
    name: MyService
    version: 2.1.0

server:
    host: 0.0.0.0
    port: 8080

features = [auth, logging, metrics]
