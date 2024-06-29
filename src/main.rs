use parser::*;
use std::env;
use std::io;
use std::process;

mod parser;

fn match_pattern(input_line: &str, pattern: &str) -> bool {
    let parsed_pattern = parse_pattern(pattern);
    println!("Parsed pattern: {:?}", parsed_pattern);
    let context = Context::new(0, 0);
    match parsed_pattern {
        Ok(p) => match_patterns(input_line, &p, &context),
        Err(e) => {
            panic!("Error parsing pattern: {}", e);
        }
    }
}

// Usage: echo <input_text> | your_grep.sh -E <pattern>
fn main() {
    if env::args().nth(1).unwrap() != "-E" {
        println!("Expected first argument to be '-E'");
        process::exit(1);
    }

    let pattern = env::args().nth(2).unwrap();
    let mut input_line = String::new();

    io::stdin().read_line(&mut input_line).unwrap();

    // Uncomment this block to pass the first stage
    if match_pattern(&input_line, &pattern) {
        process::exit(0)
    } else {
        process::exit(1)
    }
}
