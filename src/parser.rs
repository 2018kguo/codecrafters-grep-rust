#![allow(dead_code)]

use std::collections::HashMap;

use anyhow::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sequence(Vec<Pattern>);

#[derive(Debug, Clone, Eq, PartialEq)]
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
    Alternation(Vec<Sequence>, usize),
    Sequence(Vec<Pattern>),
    Backreference(usize),
}

struct ParsingContext {
    cur_capture_group: usize,
}

pub fn parse_pattern(pattern: &str) -> Result<Pattern> {
    let mut parsing_context = ParsingContext {
        cur_capture_group: 0,
    };
    parse_pattern_inner(pattern, &mut parsing_context)
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
        _ => {
            if c.is_numeric() {
                Pattern::Backreference(c.to_digit(10).unwrap() as usize)
            } else {
                Pattern::LiteralString(c.to_string())
            }
        }
    }
}

fn parse_pattern_inner(pattern_str: &str, parsing_context: &mut ParsingContext) -> Result<Pattern> {
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
                println!("parsing one or more");
                let last_pattern = patterns.pop().unwrap();
                patterns.push(Pattern::OneOrMore(Box::new(last_pattern)));
            }
            '?' => {
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
                let end_index = match negative {
                    false => index + index_of_matching_bracket,
                    true => index + index_of_matching_bracket - 1,
                };
                let character_group = &pattern_str[index + 1..end_index];
                //println!("character group: {}", character_group);
                let patterns_parsed_from_group =
                    parse_pattern_inner(character_group, parsing_context)?;
                let unwrapped_patterns = match patterns_parsed_from_group {
                    Pattern::Sequence(p) => p,
                    _ => vec![patterns_parsed_from_group.clone()],
                };
                if negative {
                    patterns.push(Pattern::NegativeCharacterGroup(unwrapped_patterns));
                } else {
                    patterns.push(Pattern::PositiveCharacterGroup(unwrapped_patterns));
                }
                index += index_of_matching_bracket;
                if negative {
                    index -= 1;
                }
            }
            '^' => patterns.push(Pattern::StartOfLine),
            '$' => patterns.push(Pattern::EndOfLine),
            '(' => {
                parsing_context.cur_capture_group += 1;
                let capture_group_num = parsing_context.cur_capture_group.clone();
                let mut sequences: Vec<Sequence> = Vec::new();
                let mut seq_index = index + 1;
                let mut current_sequence: Vec<Pattern> = Vec::new();
                let mut current_sequence_string = "".to_string();
                while pattern_str.chars().nth(seq_index).unwrap() != ')' {
                    match pattern_str.chars().nth(seq_index) {
                        Some('|') => {
                            let parsed_pattern =
                                parse_pattern_inner(&current_sequence_string, parsing_context)?;
                            current_sequence.push(parsed_pattern);
                            sequences.push(Sequence(current_sequence.clone()));
                            current_sequence = Vec::new();
                            //match parsed_pattern {
                            //    Pattern::Sequence(p) => {
                            //        sequences.push(Sequence(p));
                            //    }
                            //    _ => {
                            //        return Err(anyhow::anyhow!("Invalid pattern"));
                            //    }
                            //}
                            current_sequence_string = "".to_string();
                        }
                        Some('(') => {
                            if !current_sequence_string.is_empty() {
                                let parsed_pattern =
                                    parse_pattern_inner(&current_sequence_string, parsing_context)?;
                                current_sequence.push(parsed_pattern);
                                //match parsed_pattern {
                                //    Pattern::Sequence(p) => {
                                //        sequences.push(Sequence(p));
                                //    }
                                //    _ => {
                                //        sequences.push(Sequence(vec![parsed_pattern]));
                                //    }
                                //}
                            }
                            let index_of_matching_nested_bracket = pattern_str[seq_index..]
                                .find(')')
                                .ok_or_else(|| anyhow::anyhow!("Invalid capture group"))?;
                            let nested_capture_group_string = &pattern_str
                                [seq_index..seq_index + index_of_matching_nested_bracket + 1];
                            let parsed_pattern =
                                parse_pattern_inner(nested_capture_group_string, parsing_context)?;
                            current_sequence.push(parsed_pattern);
                            //match parsed_pattern {
                            //    Pattern::Sequence(p) => {
                            //        sequences.push(Sequence(p));
                            //    }
                            //    _ => {
                            //        sequences.push(Sequence(vec![parsed_pattern]));
                            //        //println!("invalid parsed pattern: {:?}", parsed_pattern);
                            //        //return Err(anyhow::anyhow!("Invalid pattern"));
                            //    }
                            //}
                            current_sequence_string = "".to_string();
                            seq_index += index_of_matching_nested_bracket;
                        }
                        Some(c) => {
                            current_sequence_string.push(c);
                        }
                        None => {
                            return Err(anyhow::anyhow!("Invalid pattern"));
                        }
                    }
                    seq_index += 1;
                    println!("seq index, pattern_str {} {}", seq_index, pattern_str);
                }
                // parse the last alternation from the last separator
                if !current_sequence_string.is_empty() {
                    let parsed_pattern =
                        parse_pattern_inner(&current_sequence_string, parsing_context)?;
                    //match parsed_pattern {
                    //    Pattern::Sequence(p) => {
                    //        sequences.push(Sequence(p));
                    //    }
                    //    _ => {
                    //        sequences.push(Sequence(vec![parsed_pattern]));
                    //    }
                    //}
                    current_sequence.push(parsed_pattern);
                }
                sequences.push(Sequence(current_sequence.clone()));
                patterns.push(Pattern::Alternation(sequences, capture_group_num));
                index = seq_index;
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

fn read_capture_group_string(
    capture_group_string: &str,
    capture_groups: &mut HashMap<usize, String>,
    current_capture_group_number: usize,
) -> String {
    let mut capture_group_number = current_capture_group_number;
    // base case
    if !(capture_group_string.contains('(') && capture_group_string.contains(')')) {
        let capture_group_string = capture_group_string.to_string();
        capture_groups.insert(current_capture_group_number, capture_group_string.clone());
        //println!(
        //    "inserting into capture groups at position: {} {}",
        //    capture_group_string, current_capture_group_number
        //);
        return capture_group_string;
    }
    let mut index = 0;
    let capture_group_chars: Vec<char> = capture_group_string.chars().collect();
    while index < capture_group_string.len() {
        match capture_group_chars.get(index).unwrap() {
            '(' => {
                let index_of_opening_bracket = index;
                let mut nested_capture_group_string = "".to_string();
                let mut nested_level = 1;
                while nested_level > 0 {
                    //nested_capture_group_string.push(*capture_group_chars.get(index).unwrap());
                    index += 1;
                    match capture_group_chars.get(index).unwrap() {
                        '(' => nested_level += 1,
                        ')' => nested_level -= 1,
                        _ => (),
                    }
                    if nested_level > 0 {
                        nested_capture_group_string.push(*capture_group_chars.get(index).unwrap());
                    }
                }
                let parsed_capture_group_string = read_capture_group_string(
                    &nested_capture_group_string,
                    capture_groups,
                    capture_group_number + 1,
                );
                let string_after_capture_group = if index + 1 < capture_group_string.len() {
                    &capture_group_string[index + 1..]
                } else {
                    ""
                };
                let string_before_capture_group =
                    capture_group_string[0..index_of_opening_bracket].to_string();
                let capture_group_string_with_no_parenthesis = string_before_capture_group
                    + &parsed_capture_group_string
                    + string_after_capture_group;
                capture_groups.insert(
                    current_capture_group_number,
                    capture_group_string_with_no_parenthesis,
                );
                capture_group_number = *capture_groups.keys().max().unwrap();
            }
            _ => {
                index += 1;
            }
        }
    }
    return capture_groups
        .get(&current_capture_group_number)
        .unwrap()
        .clone();
}

pub fn preprocess_backreferences(pattern: &str) -> String {
    let mut capture_groups: HashMap<usize, String> = HashMap::new();
    read_capture_group_string(pattern, &mut capture_groups, 0);
    // the raw string is treated as the 0th level
    if capture_groups.keys().len() == 1 {
        return pattern.to_string();
    }
    let mut new_pattern = pattern.to_string();
    let mut cur_level = *capture_groups.keys().max().unwrap();
    while cur_level > 0 {
        let level_minus_one_string = capture_groups.get(&(cur_level - 1)).unwrap();
        let capture_group_contents = capture_groups.get(&cur_level).unwrap().clone();
        let level_minus_one_string_with_backref_replaced =
            level_minus_one_string.replace(&format!("\\{}", cur_level), &capture_group_contents);
        capture_groups.insert(
            cur_level - 1,
            level_minus_one_string_with_backref_replaced.clone(),
        );
        let capture_group_contents_with_parenthesis = format!("({})", capture_group_contents);
        new_pattern = new_pattern.replace(
            &format!("\\{}", cur_level),
            &capture_group_contents_with_parenthesis,
        );
        cur_level -= 1;
    }
    new_pattern
}

#[derive(Debug, Clone)]
pub struct Context {
    index: usize,
    len_original_str: usize,
    capture_group_values: HashMap<usize, String>,
}

impl Context {
    pub fn new(index: usize, len_original_str: usize) -> Self {
        Self {
            index,
            len_original_str,
            capture_group_values: HashMap::new(),
        }
    }
}

pub fn find_match_within_line(input_line: &str, pattern: &Pattern) -> Option<usize> {
    for i in 0..input_line.len() {
        let mut cur_context = Context::new(i, input_line.len());
        if match_patterns(&input_line[i..], pattern, &mut cur_context, 0).0 {
            return Some(i);
        }
    }
    None
}

pub fn match_patterns(
    input_line: &str,
    pattern: &Pattern,
    context: &mut Context,
    index: usize,
) -> (bool, Vec<usize>) {
    //println!(
    //    "matching pattern: {:?} with input line: {}, and index: {}",
    //    pattern, input_line, index
    //);
    if index >= input_line.len() {
        match pattern {
            Pattern::EndOfLine => return (true, vec![0]),
            Pattern::ZeroOrOne(_) => return (true, vec![0]),
            Pattern::Sequence(p) => {
                return (p.is_empty(), vec![0]);
            }
            _ => return (false, vec![0]),
        }
    }
    let cur_input_line = &input_line[index..];
    match pattern {
        Pattern::LiteralString(s) => (cur_input_line.starts_with(s), vec![s.len()]),
        Pattern::DigitChar => {
            let next_char = cur_input_line.chars().next();
            match next_char {
                Some(c) => (c.is_numeric(), vec![1]),
                None => (false, vec![0]),
            }
        }
        Pattern::AlphanumericChar => {
            let next_char = cur_input_line.chars().next();
            match next_char {
                Some(c) => (c.is_alphanumeric(), vec![1]),
                None => (false, vec![0]),
            }
        }
        Pattern::PositiveCharacterGroup(patterns) => {
            let next_char = cur_input_line.chars().next();
            match next_char {
                Some(c) => (
                    patterns
                        .iter()
                        .any(|p| match_patterns(&c.to_string(), p, context, 0).0),
                    vec![1],
                ),
                None => (false, vec![0]),
            }
        }
        Pattern::NegativeCharacterGroup(patterns) => {
            let next_char = cur_input_line.chars().next();
            match next_char {
                Some(c) => (
                    !patterns
                        .iter()
                        .any(|p| match_patterns(&c.to_string(), p, context, 0).0),
                    vec![1],
                ),
                None => (false, vec![0]),
            }
        }
        Pattern::StartOfLine => {
            if context.index == 0 {
                return (true, vec![0]);
            }
            let next_char = input_line.chars().next();
            match next_char {
                Some(c) => (c == '\n', vec![0]),
                None => (false, vec![0]),
            }
        }
        Pattern::EndOfLine => {
            if index >= input_line.len() {
                return (true, vec![0]);
            }
            let next_char = input_line.chars().next_back();
            match next_char {
                Some(c) => (c == '\n', vec![0]),
                None => (false, vec![0]),
            }
        }
        Pattern::OneOrMore(p) => {
            // this is a greedy operator that will match as many characters as possible
            let mut index_increment = 0;
            let mut matching_increments = vec![];
            loop {
                let (match_found, _increments) =
                    match_patterns(input_line, p, context, index + index_increment);
                //if !match_found {
                //    if context.index == 0 {
                //        dbg!("match not found for {} at index {}", p, index + index_increment);
                //    }
                //    break;
                //}
                //dbg!(&_increments);
                if match_found {
                    matching_increments.push(index_increment + _increments[0]);
                } else {
                    break;
                }
                index_increment += 1;
            }
            let found = !matching_increments.is_empty();
            (found, matching_increments)
        }
        Pattern::ZeroOrOne(p) => {
            let (found, increment) = match_patterns(input_line, p, context, index);
            if found {
                (true, increment)
            } else if input_line.is_empty() {
                (true, vec![0])
            } else {
                (false, vec![0])
            }
        }
        Pattern::WildcardChar => (!input_line.is_empty(), vec![1]),
        Pattern::Alternation(sequences, capture_group_num) => {
            // return the increment of the first matching sequence
            for seq in sequences {
                let (found, increment) = match_patterns(
                    input_line,
                    &Pattern::Sequence(seq.0.clone()),
                    context,
                    index,
                );
                if found {
                    let used_inc = increment[0];
                    let input_line_consumed_by_sequence = &input_line[index..index + used_inc];
                    context.capture_group_values.insert(
                        *capture_group_num,
                        input_line_consumed_by_sequence.to_string(),
                    );
                    println!(
                        "inserting into capture groups at position: {} {}",
                        input_line_consumed_by_sequence, *capture_group_num
                    );
                    return (true, increment);
                }
            }
            (false, vec![0])
        }
        Pattern::Sequence(patterns) => {
            let (found, increment) = match_sequence(input_line, patterns, context, index, 0);
            (found, vec![increment])
            //let mut index_increment = 0;
            //for p in patterns {
            //    match p {
            //        Pattern::ZeroOrOne(_) => {
            //            let (found, match_increment) =
            //                match_patterns(input_line, p, context, index + index_increment);
            //            if !found {
            //                continue;
            //            }
            //            index_increment += match_increment[0];
            //        }
            //        Pattern::OneOrMore(_) => {
            //            // this one is tricky because it's not a greedy match.
            //            // we need to match as many characters as possible but also
            //            // backtrack if the next pattern doesn't match
            //            let mut found = false;
            //            let mut match_increment = 0;
            //            loop {
            //                let (match_found, increments) =
            //                    match_patterns(input_line, p, context, index + index_increment);
            //                if !match_found {
            //                    break;
            //                }
            //                found = true;
            //                for inc in increments {
            //                    match_increment += inc;
            //                }
            //                match_increment += increment;
            //            }
            //        }
            //        _ => {
            //            let (found, match_increment) =
            //                match_patterns(input_line, p, context, index + index_increment);
            //            if !found {
            //                return (false, vec![0]);
            //            }
            //            index_increment += match_increment[0];
            //        },
            //    }
            //    //if let Pattern::ZeroOrOne(_) = *p {
            //    //    let (found, match_increment) =
            //    //        match_patterns(input_line, p, context, index + index_increment);
            //    //    if !found {
            //    //        continue;
            //    //    }
            //    //    index_increment += match_increment;
            //    //} else {
            //    //    let (found, match_increment) =
            //    //        match_patterns(input_line, p, context, index + index_increment);
            //    //    if !found {
            //    //        return (false, 0);
            //    //    }
            //    //    index_increment += match_increment;
            //    //}
            //}
            //(true, vec![index_increment])
        }
        Pattern::Backreference(id) => {
            println!("fetching from backreference id: {}", id);
            println!("context: {:?}", context);
            println!("capture group values: {:?}", context.capture_group_values);
            if !context.capture_group_values.contains_key(id) {
                println!("backreference id not found: {}", id);
                return (false, vec![0]);
            }
            let capture_group_value = context.capture_group_values.get(id).unwrap();
            if cur_input_line.starts_with(capture_group_value) {
                (true, vec![capture_group_value.len()])
            } else {
                (false, vec![0])
            }
        }
    }
}

fn match_sequence(
    input_line: &str,
    patterns: &Vec<Pattern>,
    context: &mut Context,
    index: usize,
    depth: usize,
) -> (bool, usize) {
    println!("START OF SEQUENCE MATCH");
    println!("depth: {}", depth);
    dbg!(patterns);
    println!("---- start ---- ");
    //// backtracks if the next pattern doesn't match
    let mut index_increment = 0;
    let mut pattern_index = 0;
    for p in patterns {
        println!("in p for loop at depth: {}", depth);
        match p {
            Pattern::ZeroOrOne(_) => {
                let (found, match_increment) =
                    match_patterns(input_line, p, context, index + index_increment);
                if !found {
                    continue;
                }
                index_increment += match_increment[0];
            }
            Pattern::OneOrMore(_) => {
                // this one is tricky because it's not a greedy match.
                // we need to match as many characters as possible but also
                // backtrack if the next pattern doesn't match
                //let mut found = false;
                //let mut match_increment = 0;
                let (match_found, increments) =
                    match_patterns(input_line, p, context, index + index_increment);
                //println!("seq match found: {}", match_found);
                if context.index == 0 {
                    println!("seq increments: {:?}", increments);
                    dbg!(&context);
                }
                if !match_found {
                    return (false, 0);
                }
                let mut found = false;
                //let mut match_increment = 0;
                let reverse_sorted_increments = increments.iter().rev();
                for inc in reverse_sorted_increments.clone() {
                    let next_patterns = if pattern_index + 1 < patterns.len() {
                        patterns[pattern_index + 1..].to_vec()
                    } else {
                        vec![]
                    };
                    // TODO: fix this since this is not aware of the top level sequence, only the
                    // current nested one.
                    let next_patterns_as_sequence = Pattern::Sequence(next_patterns);
                    if context.index == 0 {
                        println!("----");
                        println!("patterns: {:?}", patterns);
                        println!("next patterns as seq: {:?}", next_patterns_as_sequence);
                        println!("reverse sorted increments: {:?}", reverse_sorted_increments);
                        println!("----");
                    }
                    let (seq_matches, _seq_increment) = match_sequence(
                        input_line,
                        &vec![next_patterns_as_sequence.clone()],
                        context,
                        index + index_increment + inc,
                        depth + 1,
                    );
                    if context.index == 0 {
                        //println!("seq matches: {}", seq_matches);
                        println!("increment and seq matches: {} {}", inc, seq_matches);
                    }
                    if seq_matches {
                        //println!("seq increment: {}", _seq_increment);
                        index_increment += inc;
                        //println!("index increment: {}", index_increment);
                        found = true;
                        if context.index == 0 {
                            println!("found: {} with inc {}", found, inc);
                            println!("capture group values: {:?}", context.capture_group_values);
                            println!("next pattersn as sequence: {:?}", next_patterns_as_sequence);
                        }
                        break;
                    }
                }
                if !found {
                    println!("context index: {}", context.index);
                    return (false, 0);
                }
                //match_increment += match_increment;
            }
            _ => {
                println!("matching pattern: {:?}", p);
                let (found, match_increment) =
                    match_patterns(input_line, p, context, index + index_increment);
                if !found {
                    //println!("pattern not found: {:?}", p);
                    return (false, 0);
                }
                index_increment += match_increment[0];
            }
        }
        pattern_index += 1;
    }
    println!("END OF SEQUENCE MATCH at depth: {}", depth);
    (true, index_increment)
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
            &mut Context::new(0, 0)
        };
    }

    #[test]
    fn test_match_single_character() {
        let input_line = "a";
        let pattern = ls!("a");
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_match_single_character_fail() {
        let input_line = "a";
        let pattern = ls!("b");
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_match_number() {
        let input_line = "123";
        let pattern = Pattern::DigitChar;
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_match_basic_sequence() {
        let input_line = "abc";
        let pattern = seq!(ls!("a"), ls!("b"), ls!("c"));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "ab";
        let pattern = seq!(ls!("a"), ls!("c"));
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "abc";
        let pattern = seq!(ls!("a"), alp!(), ls!("c"));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "abc";
        let pattern = seq!(ls!("a"), dig!(), ls!("c"));
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_one_or_more() {
        let input_line = "a";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "aa";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "b";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "";
        let pattern = Pattern::OneOrMore(Box::new(ls!("a")));
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_zero_or_one() {
        let input_line = "a";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "aa";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "b";
        let pattern = Pattern::ZeroOrOne(Box::new(ls!("a")));
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_wildcard() {
        let input_line = "a";
        let pattern = Pattern::WildcardChar;
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "aa";
        let pattern = Pattern::WildcardChar;
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "";
        let pattern = Pattern::WildcardChar;
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "a";
        let pattern = seq!(ls!("a"), Pattern::WildcardChar);
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "a?";
        let pattern = seq!(ls!("a"), Pattern::WildcardChar);
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_character_group() {
        let input_line = "a";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(ls!("a"))]);
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "b";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(ls!("a"))]);
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "a";
        let pattern = Pattern::NegativeCharacterGroup(vec![b!(ls!("a"))]);
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "b";
        let pattern = Pattern::NegativeCharacterGroup(vec![b!(ls!("a"))]);
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "a";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(Pattern::AlphanumericChar)]);
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(Pattern::AlphanumericChar)]);
        assert!(!match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "a";
        let pattern = Pattern::PositiveCharacterGroup(vec![b!(ls!("a")), b!(ls!("b"))]);
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);
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
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_alternation() {
        let input_line = "a";
        let pattern =
            Pattern::Alternation(vec![Sequence(vec![ls!("a")]), Sequence(vec![ls!("b")])], 0);
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);

        let input_line = "b";
        let pattern = Pattern::Alternation(
            vec![Sequence(vec![Pattern::Alternation(
                vec![Sequence(vec![ls!("b")])],
                0,
            )])],
            0,
        );
        assert!(match_patterns(input_line, &pattern, c!(), 0).0);
    }

    #[test]
    fn test_parse_one_or_more_pattern() {
        let pattern = parse_pattern("ca+t");
        assert_eq!(
            pattern.unwrap(),
            seq!(ls!("c"), Pattern::OneOrMore(Box::new(ls!("a"))), ls!("t"))
        );
    }

    #[test]
    fn test_read_capture_group_string() {
        let mut capture_groups: HashMap<usize, String> = HashMap::new();
        let capture_group_string = "(a)";
        let _ = read_capture_group_string(capture_group_string, &mut capture_groups, 0);
        assert_eq!(capture_groups.get(&0).unwrap(), "a");
        assert_eq!(capture_groups.get(&1).unwrap(), "a");

        capture_groups.clear();

        let capture_group_string = "(a(b(c)))";
        let _ = read_capture_group_string(capture_group_string, &mut capture_groups, 0);
        assert_eq!(capture_groups.get(&0).unwrap(), "abc");
        assert_eq!(capture_groups.get(&1).unwrap(), "abc");
        assert_eq!(capture_groups.get(&2).unwrap(), "bc");
        assert_eq!(capture_groups.get(&3).unwrap(), "c");

        capture_groups.clear();
        let capture_group_string = "(a(b(c))d)";

        let _ = read_capture_group_string(capture_group_string, &mut capture_groups, 0);
        assert_eq!(capture_groups.get(&0).unwrap(), "abcd");
        assert_eq!(capture_groups.get(&1).unwrap(), "abcd");
        assert_eq!(capture_groups.get(&2).unwrap(), "bc");
        assert_eq!(capture_groups.get(&3).unwrap(), "c");

        capture_groups.clear();

        let capture_group_string = "one (two (three) four) five";
        let _ = read_capture_group_string(capture_group_string, &mut capture_groups, 0);
        assert_eq!(capture_groups.get(&0).unwrap(), "one two three four five");
        assert_eq!(capture_groups.get(&1).unwrap(), "two three four");
        assert_eq!(capture_groups.get(&2).unwrap(), "three");

        capture_groups.clear();

        let capture_group_string = "one (two) three (four (five))";
        let _ = read_capture_group_string(capture_group_string, &mut capture_groups, 0);
        //assert_eq!(capture_groups.get(&0).unwrap(), "one two three four");
        assert_eq!(capture_groups.get(&1).unwrap(), "two");
        assert_eq!(capture_groups.get(&2).unwrap(), "four five");
        assert_eq!(capture_groups.get(&3).unwrap(), "five");
    }

    #[test]
    fn test_preprocess_backreferences() {
        let pattern = "(\\d+) (\\w+) squares and \\1 \\2 circles";
        let processed_pattern = preprocess_backreferences(pattern);
        println!("processed pattern: {}", processed_pattern);

        let pattern = "('(cat) and \\2') is the same as \\1";
        let processed_pattern = preprocess_backreferences(pattern);
        println!("processed pattern: {}", processed_pattern);
    }
}
