use shoumei::*;

fn main() {
    // The YAML file is found relative to the current file, similar to how modules are found
    let yaml = clap::load_yaml!("cli.yaml");
    let app = clap::App::from_yaml(yaml);
    let _ = app.get_matches();

    let mut loader = ModuleLoader::new(ErrorEmitter::new());
    loader.load(interpreter::ModulePath(vec![
        String::from("input"),
        String::from("test.shoumei"),
    ]));
    loader.take_error_emitter().emit_all();
}
