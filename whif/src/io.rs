use std::{
    path::PathBuf,
    fs::File,
    io::{BufRead, BufReader},
    num::ParseIntError,
};

// FIXME assert!(build::INFINITY >= 2 * upper_limit)
const INFINITY: i32 = std::i32::MAX - 1000;

#[derive(Clone, Copy, Debug)]
enum ExpectedShape {
    Line,
    Square,
    Rectangle,
}

#[derive(Clone, Copy, Debug)]
enum CommentMode {
    Implicit,
    Explicit, // FIXME pattern,
}

#[derive(Clone, Default, Debug)]
struct Metadata {
    start_line: usize,
    num_lines:  usize,
    name:       Option<String>,
}

#[derive(Debug)]
struct Parser {
    metadata:       Metadata,
    expected_shape: ExpectedShape,
    comment_mode:   CommentMode,
    rows:           Vec<Vec<i32>>,
    errors:         Vec<(usize, ParseIntError)>,
    num_tokens:     usize,
    current_row:    Vec<i32>,
    curly_level:    i16,
    proper_level:   i16,
}

impl Parser {
    fn new() -> Self {
        Parser {
            metadata:       Metadata::default(),
            expected_shape: ExpectedShape::Square,
            comment_mode:   CommentMode::Implicit,
            rows:           Vec::new(),
            errors:         Vec::new(),
            num_tokens:     0,
            current_row:    Vec::new(),
            curly_level:    0,
            proper_level:   0,
        }
    }

    fn parse_line(&mut self, line: &str) -> Option<Metadata> {
        for word in line.split_whitespace() {
            if self.num_tokens == 0 {
                if word.starts_with(|c: char| c == '-' || c.is_numeric()) {
                    self.proper_level = 0;
                } else if word.starts_with('{') {
                    self.proper_level = 2; // FIXME ExpectedShape
                } else {
                    break // FIXME CommentMode
                }
            }

            if self.proper_level > 0 {
                for token in word.split_terminator(',') {
                    self.parse_curly_token(token);
                    self.num_tokens += 1;
                }
            } else {
                if word == "inf" {
                    self.current_row.push(INFINITY);
                } else {
                    match word.parse() {
                        Ok(elt) => self.current_row.push(elt),
                        Err(err) => self.errors.push((self.num_tokens, err)),
                    }
                }
                self.num_tokens += 1;
            }
        }

        if self.proper_level > 0 {
            if self.curly_level < 1 {
                self.rows.push(self.current_row.clone());
                self.current_row.clear();
                return Some(self.metadata.clone())
            }
        } else {
            if self.current_row.is_empty() {
                if !self.rows.is_empty() {
                    return Some(self.metadata.clone())
                }
            } else {
                self.rows.push(self.current_row.clone());
                self.current_row.clear();
            }
        }

        None
    }

    fn parse_curly_token(&mut self, mut token: &str) {
        if token.starts_with('{') {
            if !self.current_row.is_empty() {
                self.rows.push(self.current_row.clone());
                self.current_row.clear();
            }

            if token.starts_with("{{") {
                self.curly_level += 2;
            } else {
                self.curly_level += 1;
            }

            token = token.trim_start_matches('{');
        }

        let do_parse = self.curly_level == self.proper_level;

        if token.ends_with('}') {
            if token.ends_with("}}") {
                self.curly_level -= 2;
            } else {
                self.curly_level -= 1;
            }
            token = token.trim_end_matches('}');
        }

        if do_parse && !token.is_empty() {
            if token == "inf" {
                self.current_row.push(INFINITY);
            } else {
                match token.parse() {
                    Ok(elt) => self.current_row.push(elt),
                    Err(err) => self.errors.push((self.num_tokens, err)),
                }
            }
        }
    }
}

pub fn load_vector<P: Into<PathBuf>>(path: P) -> Vec<i32> {
    let file = BufReader::new(File::open(path.into()).unwrap());
    let mut parser = Parser::new();

    parser.expected_shape = ExpectedShape::Line;

    for line in file.lines().map(|l| l.unwrap()) {
        if let Some(metadata) = parser.parse_line(line.as_str()) {
            break
        }
    }

    if let Some(row) = parser.rows.first() {
        row.clone()
    } else {
        Vec::new() // FIXME error
    }
}

pub fn load_square_matrix<P: Into<PathBuf>>(path: P) -> (Vec<i32>, usize) {
    let file = BufReader::new(File::open(path.into()).unwrap());
    let mut parser = Parser::new();

    parser.expected_shape = ExpectedShape::Square;

    for line in file.lines().map(|l| l.unwrap()) {
        if let Some(metadata) = parser.parse_line(line.as_str()) {
            break
        }
    }

    let dim = parser.rows.len();
    assert!(dim > 1); // FIXME error

    let mut vec = Vec::with_capacity(dim * dim);

    for col in 0..dim {
        for row in parser.rows.iter() {
            vec.push(row.get(col).copied().unwrap_or(0));
        }
    }

    (vec, dim)
}
