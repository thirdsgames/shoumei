use shoumei::parser::Ranged;
use shoumei::*;

fn main() {
    // The YAML file is found relative to the current file, similar to how modules are found
    let yaml = clap::load_yaml!("cli.yaml");
    let app = clap::App::from_yaml(yaml);
    let _ = app.get_matches();

    let mut module_loader = ModuleLoader::new(ErrorEmitter::new());
    module_loader.load(parser::ModulePath(vec![
        String::from("input"),
        String::from("test"),
    ]));
    if !module_loader.take_error_emitter().emit_all() {
        // No errors. Execute some test functions.
        
        test_func(&module_loader, "testfn");
        test_func(&module_loader, "test_two");
        test_func(&module_loader, "test_three");
    }
}

fn test_func<'ml>(module_loader: &'ml ModuleLoader, function: impl ToString) {
    let module_path = parser::ModulePath(vec![
        String::from("input"),
        String::from("test"),
    ]);
    let range = module_loader.definition(&parser::QualifiedName {
        module_path: module_path.clone(),
        name: function.to_string(),
        range: parser::Location { line: 0, col: 0 }.into(),
    }).unwrap().range();
    print_evaluated(
        &module_loader,
        runtime::value::Function::from_name(
            &module_loader,
            parser::QualifiedName {
                module_path,
                name: function.to_string(),
                range,
            },
        )
        .unwrap()
        .apply_zero_args()
        .into(),
    );
    println!();
}

fn print_evaluated<'ml>(module_loader: &'ml ModuleLoader, value: runtime::value::ValueRef<'ml>) {
    let result = runtime::Runtime::evaluate(&module_loader, value);
    match result {
        runtime::value::Value::Data(data) => {
            print!("{}", data.type_ctor);
            for param in data.args {
                print!(" (");
                print_evaluated(module_loader, param);
                print!(")");
            }
        }
        runtime::value::Value::Function(func) => {
            println!("<function of arity {}>", func.arity())
        }
        runtime::value::Value::Lambda(lambda) => {
            println!("<lambda of arity {}>", lambda.params.len())
        }
        runtime::value::Value::Apply(_) => panic!("should never return an `Apply`"),
        runtime::value::Value::Let(_) => panic!("should never return a `Let`"),
    }
}
