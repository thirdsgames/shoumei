use std::{
    io::{BufRead, BufReader},
};

use shoumei::*;

fn parse() -> DiagnosticResult<()> {
    let resource = Resource::new(String::from("input/test.shoumei"));
    let f = resource.open_file();

    f.bind(|f| {
        let mut lines = Vec::new();
        for (line, line_number) in BufReader::new(f).lines().zip(0..) {
            match line {
                Ok(line) => {
                    lines.push(line);
                }
                Err(_) => {
                    return DiagnosticResult::fail(ErrorMessage::new(
                        format!("file contained invalid UTF-8 on line {}", line_number + 1),
                        Severity::Error,
                        Diagnostic::in_file(resource),
                    ));
                }
            }
        }
        DiagnosticResult::ok(())
    })
}

fn main() {
    // The YAML file is found relative to the current file, similar to how modules are found
    let yaml = clap::load_yaml!("cli.yaml");
    let app = clap::App::from_yaml(yaml);
    let _ = app.get_matches();

    let result = parse();
    result.print_messages();
}
