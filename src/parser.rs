#![allow(dead_code)]

use anyhow::Result;

#[derive(Debug, Clone)]
pub struct Sequence(Vec<Pattern>);

#[derive(Debug, Clone)]
pub enum Pattern {
    LiteralString(String),
    DigitChar,
    AlphanumericChar,
    PositiveCharacterGroup(Vec<Pattern>),
    NegativeCharacterGroup(Vec<Pattern>),
    StartOfLine,
    EndOfLine,
    OneOrMore(Box<Pattern>),
    ZeroOrOne(Box<Pattern>),
    WildcardChar,
    Alternation(Vec<Sequence>),
    Sequence(Vec<Pattern>),
}

pub fn parse_pattern(pattern: &str) -> Result<Pattern> {
    parse_pattern_inner(pattern)
}

fn parse_escape_char(c: char) -> Pattern {
    match c {
        'd' => Pattern::DigitChar,
        'w' => Pattern::AlphanumericChar,
        's' => Pattern::PositiveCharacterGroup(vec![
            Pattern::LiteralString(" ".to_string()),
            Pattern::LiteralString("\t".to_string()),
        ]),
        'S' => Pattern::NegativeCharacterGroup(vec![
            Pattern::LiteralString(" ".to_string()),
            Pattern::LiteralString("\t".to_string()),
        ]),
        _ => Pattern::LiteralString(c.to_string()),
    }
}

fn parse_pattern_inner(pattern_str: &str) -> Result<Pattern> {
    let mut patterns = Vec::new();
    let mut index = 0;
    let pattern_chars: Vec<char> = pattern_str.chars().collect();
    while index < pattern_str.len() {
        match pattern_str.chars().nth(index).unwrap() {
            '.' => patterns.push(Pattern::WildcardChar),
            '\\' => {
                index += 1;
                let c = pattern_chars
                    .get(index)
                    .ok_or_else(|| anyhow::anyhow!("Invalid escape character"))?;
                patterns.push(parse_escape_char(*c));
            }
            '+' => {
                let last_pattern = patterns.pop().unwrap();
                patterns.push(Pattern::OneOrMore(Box::new(last_pattern)));
            }
            '*' => {
                let last_pattern = patterns.pop().unwrap();
                patterns.push(Pattern::ZeroOrOne(Box::new(last_pattern)));
            }
            '[' => {
                let mut negative = false;
                let next_char = pattern_str.chars().nth(index + 1);
                let closing_bracket = ']';
                let index_of_matching_bracket = pattern_str[index..]
                    .find(closing_bracket)
                    .ok_or_else(|| anyhow::anyhow!("Invalid character group"))?;

                match next_char {
                    Some('^') => {
                        negative = true;
                        index += 1;
                    }
                    None => return Err(anyhow::anyhow!("Invalid character group")),
                    _ => (),
                }
                let character_group = &pattern_str[index + 1..index + index_of_matching_bracket];
                let patterns_parsed_from_group = parse_pattern_inner(character_group)?;
                let unwrapped_patterns = match patterns_parsed_from_group {
                    Pattern::Sequence(p) => p,
                    _ => vec![patterns_parsed_from_group.clone()],
                };
                if negative {
                    patterns.push(Pattern::NegativeCharacterGroup(unwrapped_patterns));
                } else {
                    patterns.push(Pattern::PositiveCharacterGroup(unwrapped_patterns));
                }
                index = index_of_matching_bracket;
            }
            '^' => patterns.push(Pattern::StartOfLine),
            '$' => patterns.push(Pattern::EndOfLine),
            '(' => {
                unimplemented!();
                //let mut sequences = Vec::new();
                //while let Some(c) = pattern_chars.next() {
                //    let mut current_sequence_string = "".to_string();
                //    match c {
                //        ')' => {
                //            let parsed_pattern = parse_pattern_inner(&current_sequence_string)?;
                //            sequences.push(Box::new(parsed_pattern));
                //            break;
                //        }
                //        '|' => {
                //            let parsed_pattern = parse_pattern_inner(&current_sequence_string)?;
                //            sequences.push(Box::new(parsed_pattern));
                //        }
                //        _ => {
                //            current_sequence_string.push(c);
                //        }
                //    }
                //}
                //let sequence = Sequence(sequences);
                //patterns.push(Pattern::Alternation(Box::new(sequence)));
            }
            '|' => {
                unimplemented!();
            }
            _ => {
                let c = pattern_chars.get(index).unwrap();
                patterns.push(Pattern::LiteralString(c.to_string()))
            }
        }
        index += 1;
    }
    if patterns.len() == 1 {
        Ok(patterns.pop().unwrap())
    } else {
        Ok(Pattern::Sequence(patterns.into_iter().collect()))
    }
}

#[derive(Debug, Clone)]
pub struct Context {
    index: usize,
    len_original_str: usize,
}

impl Context {
    pub fn new(index: usize, len_original_str: usize) -> Self {
        Self {
            index,
            len_original_str,
        }
    }
}

pub fn find_match_within_line(input_line: &str, pattern: &Pattern) -> Option<usize> {
    for i in 0..input_line.len() {
        let cur_context = Context::new(i, input_line.len());
        if match_patterns(&input_line[i..], pattern, &cur_context) {
            return Some(i);
        }
    }
    None
}

pub fn match_patterns(input_line: &str, pattern: &Pattern, context: &Context) -> bool {
    //println!("matching pattern: {:?} with input line: {}", pattern, input_line);
    match pattern {
        Pattern::LiteralString(s) => input_line.starts_with(s),
        Pattern::DigitChar => {
            let next_char = input_line.chars().next();
            match next_char {
                Some(c) => c.is_numeric(),
                None => false,
            }
        }
        Pattern::AlphanumericChar => {
            let next_char = input_line.chars().next();
            match next_char {
                Some(c) => c.is_alphanumeric(),
                None => false,
            }
        }
        Pattern::PositiveCharacterGroup(patterns) => {
            let next_char = input_line.chars().next();
            match next_char {
                Some(c) => patterns
                    .iter()
                    .any(|p| match_patterns(&c.to_string(), p, context)),
                None => false,
            }
        }
        Pattern::NegativeCharacterGroup(patterns) => {
            let next_char = input_line.chars().next();
            match next_char {
                Some(c) => !patterns
                    .iter()
                    .any(|p| match_patterns(&c.to_string(), p, context)),
                None => false,
            }
        }
        Pattern::StartOfLine => {
            println!("context is {:?}, input string is {}", context, input_line);
            if context.index == 0 {
                return true;
            }
            let next_char = input_line.chars().next();
            match next_char {
                Some(c) => c == '\n',
                None => false,
            }
        }
        Pattern::EndOfLine => {
            if context.index >= context.len_original_str {
                return true;
            }
            let next_char = input_line.chars().next_back();
            match next_char {
                Some(c) => c == '\n',
                None => false,
            }
        }
        Pattern::OneOrMore(p) => {
            let mut found = false;
            for i in 0..input_line.len() {
                if match_patterns(&input_line[i..], p, context) {
                    found = true;
                    break;
                }
            }
            found
        }
        Pattern::ZeroOrOne(p) => match_patterns(input_line, p, context) || input_line.is_empty(),
        Pattern::WildcardChar => !input_line.is_empty(),
        Pattern::Alternation(sequences) => sequences
            .iter()
            .any(|s| s.0.iter().all(|p| match_patterns(input_line, p, context))),
        Pattern::Sequence(patterns) => {
            let mut input_line = input_line;
            let mut index_in_line = context.index;
            for p in patterns {
                let new_ctx = Context::new(index_in_line, context.len_original_str);
                //println!("index in line: {}, input line: {}", index_in_line, input_line);
                if let Pattern::ZeroOrOne(_) = *p {
                    if !match_patterns(input_line, p, &new_ctx) {
                        continue;
                    }
                } else if !match_patterns(input_line, p, &new_ctx) {
                    return false;
                }
                let increment = match p {
                    Pattern::LiteralString(s) => s.len(),
                    Pattern::StartOfLine => 0,
                    Pattern::EndOfLine => 0,
                    _ => 1,
                };
                input_line = &input_line[increment..];
                index_in_line += increment;
                //println!("pattern matched: {:?}", p);
                //println!("index in line: {}, input line: {}", index_in_line, input_line);
            }
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! ls {
        ($s:expr) => {
            Pattern::LiteralString($s.to_string())
        };
    }

    macro_rules! seq {
        ($($p:expr),*) => {
            Pattern::Sequence(vec![$($p),*])
        };
    }

    macro_rules! dig {
        () => {
            Pattern::DigitChar
        };
    }

    macro_rules! alp {
        () => {
            Pattern::AlphanumericChar
        };
    }

    macro_rules! b {
        ($p:expr) => {
            $p
        };
    }

    macro_rules! c {
        () => {
            &Context::new(0, 0)
        };
    }

    #[test]
    fn test_match_single_character() {
        let input_line = "a";
        let pattern = ls!("a");
        assert!(match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_match_single_character_fail() {
        let input_line = "a";
        let pattern = ls!("b");
        assert!(!match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_match_number() {
        let input_line = "123";
        let pattern = Pattern::DigitChar;
        assert!(match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_match_basic_sequence() {
        let input_line = "abc";
        let pattern = seq!(ls!("a"), ls!("b"), ls!("c"));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "ab";
        let pattern = seq!(ls!("a"), ls!("c"));
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "abc";
        let pattern = seq!(ls!("a"), alp!(), ls!("c"));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "abc";
        let pattern = seq!(ls!("a"), dig!(), ls!("c"));
        assert!(!match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_one_or_more() {
        let input_line = "a";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "aa";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "b";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(!match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_zero_or_one() {
        let input_line = "a";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "aa";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "b";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(!match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_wildcard() {
        let input_line = "a";
        let pattern = Pattern::WildcardChar;
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "aa";
        let pattern = Pattern::WildcardChar;
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "";
        let pattern = Pattern::WildcardChar;
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "a";
        let pattern = seq!(ls!("a"), Pattern::WildcardChar);
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "a?";
        let pattern = seq!(ls!("a"), Pattern::WildcardChar);
        assert!(match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_character_group() {
        let input_line = "a";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(ls!("a"))]);
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "b";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(ls!("a"))]);
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "a";
        let pattern = Pattern::NegativeCharacterGroup(vec![b!(ls!("a"))]);
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "b";
        let pattern = Pattern::NegativeCharacterGroup(vec![b!(ls!("a"))]);
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "a";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(Pattern::AlphanumericChar)]);
        assert!(match_patterns(input_line, &pattern, c!()));

        let input_line = "";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(Pattern::AlphanumericChar)]);
        assert!(!match_patterns(input_line, &pattern, c!()));

        let input_line = "a";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(ls!("a")), b!(ls!("b"))]);
        assert!(match_patterns(input_line, &pattern, c!()));
    }

    #[test]
    fn test_combined() {
        let input_line = "100 dog";
        // " dog" would actually be parsed as individual characters but this should be equivalent
        // for the purposes of this test
        let pattern = seq!(
            Pattern::DigitChar,
            Pattern::DigitChar,
            Pattern::DigitChar,
            ls!(" dog")
        );
        assert!(match_patterns(input_line, &pattern, c!()));
    }
}
