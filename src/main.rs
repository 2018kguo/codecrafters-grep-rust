use parser::*;
use std::env;
use std::io;
use std::process;

mod parser;

fn match_pattern(input_line: &str, pattern: &str) -> bool {
    //let preprocessed_pattern = preprocess_backreferences(pattern);
    //println!("Preprocessed pattern: {}", preprocessed_pattern);
    let parsed_pattern = parse_pattern(pattern);
    //println!("pattern: {}", pattern);
    println!("Parsed pattern: {:?}", parsed_pattern);
    match parsed_pattern {
        Ok(p) => find_match_within_line(input_line, &p).is_some(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match_pattern() {
        //let preprocessed_pattern = "[a] [x]";
        //let _parsed_pattern = parse_pattern(preprocessed_pattern);
        //println!("Parsed pattern: {:?}", _parsed_pattern);

        //let pattern = "('(cat) and \\2') is the same as \\1";
        //let parsed_pattern = parse_pattern(pattern);
        //println!("Parsed pattern: {:?}", parsed_pattern);

        //let input_line = "'cat and cat' is the same as 'cat and cat'";
        //let result = find_match_within_line(input_line, &parsed_pattern.unwrap());
        //println!("Result: {:?}", result);

        //let pattern = "one (two (three)) four";
        //let parsed_pattern = parse_pattern(pattern);
        //println!("Parsed pattern: {:?}", parsed_pattern);

        //let pattern = "d+d";
        //let parsed_pattern = parse_pattern(pattern);
        //println!("Parsed pattern: {:?}", parsed_pattern);
        //let result = find_match_within_line("ddc", &parsed_pattern.unwrap());
        //println!("Result: {:?}", result);

        //let pattern = "(([abc]+)-([def]+)) is \\1, not ([^xyz]+), \\2, or \\3";
        //let parsed_pattern = parse_pattern(pattern);
        //println!("Parsed pattern: {:?}", parsed_pattern);
        //let result = find_match_within_line("abc-def is abc-def, not efg", &parsed_pattern.unwrap());
        //println!("Result: {:?}", result);

        let pattern = "([^a]+) b";
        let parsed_pattern = parse_pattern(pattern);
        println!("Parsed pattern: {:?}", parsed_pattern);
        let result = find_match_within_line("d b", &parsed_pattern.unwrap());
        println!("Result: {:?}", result);
    }
}
