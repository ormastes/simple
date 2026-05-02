## Part 15: Example Usage

### 15.1 Basic 3D Scene

```simple
use graphics.*
use graphics.math.*
use graphics.scene.*
use graphics.render.*

fn main():
    # Create scene
    let mut scene = Scene::new("My Scene")

    # Create cube mesh
    let cube_mesh = scene.resource_manager.load_mesh(Mesh::create_cube(1.0))
    let cube_material = scene.resource_manager.load_material(
        Material::PBR(PBRMaterial::preset_gold())
    )

    # Create scene node
    let cube_node = scene.create_node("Cube")
    scene.get_node_mut(cube_node).set_transform(
        Transform::new()
            .with_position(Vec3::new(0.0, 0.0, 0.0))
            .with_rotation(Quaternion::from_euler(0.0, 0.0, 0.0))
    )
    scene.get_node_mut(cube_node).add_component(
        Component::MeshRenderer(cube_mesh, cube_material)
    )

    # Add light
    let light_node = scene.create_node("Sun")
    scene.get_node_mut(light_node).add_component(
        Component::Light(Light::Directional(
            DirectionalLight::new(
                Vec3::new(-0.5, -1.0, -0.3).normalize(),
                Color::white(),
                1.5
            )
        ))
    )

    # Create camera
    let camera = Camera::perspective_standard(16.0 / 9.0)
        .with_position(Vec3::new(0.0, 2.0, 5.0))
        .look_at(Vec3::zero(), Vec3::unit_y())

    # Create renderer
    let mut renderer = Renderer3D::new(1920, 1080)

    # Render
    renderer.render(scene, camera)
```

### 15.2 Scene with UI Integration

```simple
use ui.*
use graphics.*

fn build_ui(tree: &mut ElementTree) -> Element:
    let scene = create_game_scene()
    let camera = create_game_camera()

    return Column::new(tree.alloc_id())
        .child(
            Scene3D::new(tree.alloc_id(), 1280, 720)
                .with_scene(scene)
                .with_camera(camera)
                .with_controls()
                .to_element()
        )
        .to_element()

fn main():
    let mut app = Application::new("Game")
        .window_size(1280, 720)

    app.set_root(build_ui(&mut app.element_tree))
    app.run()
```

---

