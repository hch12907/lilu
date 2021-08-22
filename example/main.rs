mod lexer_gen;

use lexer_gen::*;

fn main() {
    let patterns = include_str!("patterns.txt");
    match LexerGenerator::new(patterns) {
        Ok(gen) => {
            let generated = gen.generate();
            println!("{}", generated)
        },
        Err(e) => match e {
            GeneratorError::EmptyName(line) =>
                println!("Empty name at line {}", line+1),
            GeneratorError::EmptyPattern(line) =>
                println!("Empty pattern at line {}", line+1),
            GeneratorError::InvalidPatternType(line) =>
                println!("Invalid pattern at line {}", line+1),
            GeneratorError::InvalidPatternFixed(line) =>
                println!("Invalid fixed pattern at line {}", line+1),
            GeneratorError::InvalidPatternRegex(line, reg) =>
                println!("Invalid regex pattern at line {}: {:?}", line+1, reg),
            GeneratorError::MissingPattern(line) =>
                println!("Missing pattern at line {}", line+1),
            GeneratorError::NameExists(line) =>
                println!("Redefinition of pattern at line {}", line+1),
            GeneratorError::PatternExists(line) =>
                println!("Found existing pattern at line {}", line+1),
        }
    };
}
