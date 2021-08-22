use regex;
use std::cmp::Ordering;
use std::collections::HashSet;

/// The errors that can be generated when an invalid pattern file is provided
/// to the generator.
#[derive(Clone, Debug, PartialEq)]
pub enum GeneratorError {
    /// This error is given when an unnamed pattern is found.
    EmptyName(usize),
    /// This error is given when an empty pattern is found.
    EmptyPattern(usize),
    /// This error is given when a pattern is found to be of an unknown type.
    /// Right now there are 2 types: `"fixed"` pattern and `/regex/` pattern.
    InvalidPatternType(usize),
    /// This error is given when a fixed pattern is found to be invalid, such
    /// as it being empty
    #[allow(unused)] InvalidPatternFixed(usize),
    /// This error is given when a regex pattern is found to be invalid.
    /// The `Error` from the regex crate is provided for more information on the
    /// exact error.
    InvalidPatternRegex(usize, regex::Error),
    /// This error is given when a line contains only the name. The difference
    /// between this and `EmptyPattern` is that this error indicates that not even
    /// `:=` is found in the faulty line.
    MissingPattern(usize),
    /// This error is generated when there exists a pattern with the same name.
    NameExists(usize),
    /// This error is generated when the pattern is already used, albeit with a
    /// different name.
    PatternExists(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pattern {
    Fixed(Box<str>),
    Regex(Box<str>),
}

/// A lexer generator that receives a pattern file that describes various kinds
/// of patterns along with their names, and generates a lexer based on that.
/// This lexer will implement `Iterator` that generates `(Span, Token)`.
///
/// The grammar of a pattern file is as follows:
///
/// ```
/// # .*                ; lines beginning with a "#" is a comment
/// <name> := "[char]+" ; this is a fixed pattern
/// <name> := /[char]+/ ; this is a regex pattern
/// ```
///
/// Other than a lexer, an enum `Token` will also be generated.
/// For example, given the following pattern file:
///
/// ```
/// Multiply := "*"
/// Exponent := "**"
/// Integer  := /([0-9]+)/
/// ```
///
/// The resulting `Token` enum will be:
///
/// ```
/// enum Token {
///     Multiply,
///     Exponent,
///     Integer(String),
///     Unknown(char),
/// }
/// ```
///
/// Notice that regex patterns will *always* carry a String, thus a capture group
/// is always needed for regex patterns. Also notice that `Unknown(char)` is
/// always added, for when an unknown character matching none of the patterns is
/// encountered.
///
/// For the "fixed" patterns, the lexer is greedy. Again using the above pattern
/// file as example, given the input `***`, the resulting tokens will be
/// `[Exponent, Multiply]`.
/// 
/// If the name begins with `_`, the generated lexer will accept tokens matching
/// the pattern, but the token will be disposed.
pub struct LexerGenerator {
    map: Vec<(Option<String>, Pattern)>,
}

impl LexerGenerator {
    /// Create a new lexer generator given a pattern file. For more information
    /// on the pattern file and the generated lexer, look at the documentation
    /// for `LexerGenerator` itself.
    pub fn new(pattern_file: &str) -> Result<Self, GeneratorError> {
        let mut map_check_name = HashSet::new();
        let mut map_check_pat = HashSet::new();
        let mut map = Vec::new();

        for (line_no, line) in pattern_file.lines().enumerate() {
            let line = line.trim();
            
            if line.is_empty() || line.starts_with('#') {
                continue
            }

            let mut split_line = line.split(":=");
            let name = split_line.next().unwrap().trim();
            let pattern = split_line.next()
                .ok_or(GeneratorError::MissingPattern(line_no))?
                .trim();
            
            if name.is_empty() {
                Err(GeneratorError::EmptyName(line_no))?
            }

            if pattern.is_empty() {
                Err(GeneratorError::EmptyPattern(line_no))?
            }

            let pattern = if pattern.starts_with('/') && pattern.ends_with('/') {
                let pattern = pattern.trim_matches('/');
                
                regex::Regex::new(pattern)
                    .map_err(|e| GeneratorError::InvalidPatternRegex(line_no, e))?;

                let mut regex_pat = "^".to_string();
                regex_pat.push_str(pattern);

                Pattern::Regex(regex_pat.into_boxed_str())
            } else if pattern.starts_with('"') && pattern.ends_with('"') {
                let pattern = pattern.trim_matches('"')
                    .replace("\\n", "\n")
                    .replace("\\t", "\t")
                    .replace("\\r", "\r")
                    .replace("\\0", "\0")
                    .replace("\\\\", "\\");

                if pattern.is_empty() {
                    Err(GeneratorError::InvalidPatternFixed(line_no))?
                }

                Pattern::Fixed(pattern.into_boxed_str())
            } else {
                Err(GeneratorError::InvalidPatternType(line_no))?
            };

            if (!name.starts_with('_') && !map_check_name.insert(name.to_owned()))
                || name == "Unknown" 
            {
                Err(GeneratorError::NameExists(line_no))?
            };

            if !map_check_pat.insert(pattern.clone()) {
                Err(GeneratorError::PatternExists(line_no))?
            }

            if !name.starts_with('_') {
                map.push((Some(name.to_owned()), pattern))
            } else {
                map.push((None, pattern))
            }
        }

        Ok(Self { map })
    }

    /// Generate a lexer in the form of Rust code.
    /// The generated code will always contain the definition of `Span`,
    /// `Lexer`, and `Token`.
    pub fn generate(self) -> String {
        let mut flat_map = self.map;
        flat_map.sort_by(|(lhs_name, lhs_pat), (rhs_name, rhs_pat)| {
            match (lhs_pat, rhs_pat) {
                (Pattern::Fixed(x), Pattern::Fixed(y)) => match (lhs_name, rhs_name) {
                    (None, None) | (Some(_), Some(_)) => x.cmp(y).reverse(),
                    (Some(_), None) => Ordering::Greater,
                    (None, Some(_)) => Ordering::Less,
                }
                (Pattern::Fixed(_), Pattern::Regex(_)) => Ordering::Less,
                (Pattern::Regex(_), Pattern::Fixed(_)) => Ordering::Greater,
                (Pattern::Regex(_), Pattern::Regex(_)) => match (lhs_name, rhs_name) {
                    (None, Some(_)) => Ordering::Less,
                    (Some(_), None) => Ordering::Greater,
                    (None, None) | (Some(_), Some(_)) => Ordering::Equal,
                }
            }
        });

        const HEADER: &'static str = r#"// This file is automatically generated.
use regex::Regex;
use std::str::Chars;

pub struct Lexer<'a> {
    src: Chars<'a>,
    location: Span,
    regexes: Vec<Regex>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}

impl<'a> Lexer<'a> {
    pub fn current_location(&self) -> Span {
        self.location.clone()
    }

    fn eat(&mut self) {
        let c = self.src.next().unwrap();
        self.location.offset += 1;
        match c {
            '\n' => {
                self.location.column = 0;
                self.location.line += 1;
            },
            _ => self.location.column += 1,
        }
    }
}
"#;

        const TOKEN_ENUM_HEADER: &'static str = r#"
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
"#;

        const TOKEN_ENUM_FOOTER: &'static str = r#"
    Unknown(char),
}
"#;

        let mut token_enum = String::from(TOKEN_ENUM_HEADER);
        for (id, pat) in &flat_map {
            let id = match id {
                Some(i) => i,
                None => continue,
            };

            if let Pattern::Fixed(_) = pat {
                token_enum.push_str("    ");
                token_enum.push_str(id.as_str());
                token_enum.push_str(",\n");
            } else {
                token_enum.push_str("    ");
                token_enum.push_str(id.as_str());
                token_enum.push_str("(String),\n");
            }
        }
        token_enum.push_str(TOKEN_ENUM_FOOTER);

        const LEXER_NEW: &'static str = r#"
impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        let mut regexes = Vec::new();
%regexes%
        Lexer { src: src.chars(), location: Span { line: 0, column: 0, offset: 0 }, regexes }
    }
}
"#;
        let mut regexes_vec = String::new();
        for (_id, pat) in &flat_map {
            let depth = "        ";
            match pat {
                Pattern::Regex(r) => {
                    regexes_vec.push_str(depth);
                    regexes_vec.push_str(&format!(
                        "regexes.push(Regex::new(r#\"{}\"#).unwrap());\n",
                        r
                    ));
                },
                _ => (),
            }
        }
        let regexes_vec = LEXER_NEW.replace("%regexes%", &regexes_vec);

        const ITERATOR_IMPL_HEADER: &'static str = r#"
impl<'a> Iterator for Lexer<'a> {
    type Item = (Span, Token);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let location = self.current_location();
"#;

        const ITERATOR_IMPL_FOOTER: &'static str = r#"
            else {
                if self.src.as_str().is_empty() {
                    return None
                } else {
                    return Some((location, Token::Unknown(self.src.next().unwrap())))
                }
            }
        }
    }
}
"#;

        let mut iterator_impl = String::from(ITERATOR_IMPL_HEADER);
        let mut first_regex = None;
        for (i, (id, pat)) in flat_map.iter().enumerate() {
            let depth = "            "; // 12

            // beginning of an if-elif-else statement
            if i == 0 {
                iterator_impl.push_str(depth);
                iterator_impl.push_str("if ");
            } else {
                iterator_impl.push_str(depth);
                iterator_impl.push_str("else if ");
            };

            // condition and body of the if statement
            match pat {
                Pattern::Fixed(f) => {
                    iterator_impl.push_str(&format!("self.src.as_str().starts_with(r#\"{}\"#) {{\n", f));
                    let depth = "                "; // 16
                    for _ in 0..f.len() {
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str("self.eat();\n");
                    }

                    if let Some(id) = id {
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str(&format!("return Some((location, Token::{}))\n", id));
                    }

                    let depth = "            "; // 12
                    iterator_impl.push_str(depth);
                    iterator_impl.push_str("}\n")
                },
                Pattern::Regex(_r) => {
                    if first_regex.is_none() {
                        first_regex = Some(i);
                    }

                    let regex_idx = i - first_regex.unwrap();

                    iterator_impl.push_str(&format!(
                        "self.regexes[{}].is_match(self.src.as_str()) {{\n",
                        regex_idx
                    ));

                    let depth = "                "; // 16
                    if id.is_some() {
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str(&format!(
                            "let captured = self.regexes[{}].captures(self.src.as_str()).unwrap();\n",
                            regex_idx
                        ));
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str("let matched = captured.get(0).unwrap();\n");
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str("let result = captured.get(1).unwrap();\n");
                    } else {
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str(&format!(
                            "let matched = self.regexes[{}].find(self.src.as_str()).unwrap();\n",
                            regex_idx
                        ));
                    }

                    iterator_impl.push_str(depth);
                    iterator_impl.push_str("for _ in 0..matched.as_str().len() {\n");
                    iterator_impl.push_str(depth);
                    iterator_impl.push_str("    self.eat();\n");
                    iterator_impl.push_str(depth);
                    iterator_impl.push_str("}\n");

                    if let Some(id) = id {
                        iterator_impl.push_str(depth);
                        iterator_impl.push_str(&format!(
                            "return Some((location, Token::{}(result.as_str().to_string())))\n",
                            id
                        ));
                    }

                    let depth = "            "; // 12
                    iterator_impl.push_str(depth);
                    iterator_impl.push_str("}\n");
                },
            };   
        }

        iterator_impl.push_str(ITERATOR_IMPL_FOOTER);

        [HEADER, token_enum.as_str(), regexes_vec.as_str(), iterator_impl.as_str()].concat()
    }
}
