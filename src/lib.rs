use std::fmt::{Display, Formatter};
use std::str::FromStr;

/// Interface for constructing S-expressions
pub trait SexprFactory {
    /// The type being constructed
    type Sexpr;

    /// intermediate integer representation during parsing
    type Integer: FromStr;

    /// intermediate float representation during parsing
    type Float: FromStr;

    /// construct an integer value
    fn int(x: Self::Integer) -> Self::Sexpr;

    /// construct a floating point value
    fn float(x: Self::Float) -> Self::Sexpr;

    /// construct a symbol
    fn symbol(x: &str) -> Self::Sexpr;

    /// construct a string
    fn string(x: &str) -> Self::Sexpr;

    /// construct a list
    fn list(x: Vec<Self::Sexpr>) -> Self::Sexpr;

    /// construct a pair
    fn pair(a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr;

    /// construct a quotation
    fn quote(x: Self::Sexpr) -> Self::Sexpr {
        Self::list(vec![Self::symbol("quote"), x])
    }
}

pub type Result<'i, T> = std::result::Result<T, Error<'i>>;

#[derive(Debug, PartialEq)]
pub enum Error<'i> {
    UnexpectedEOF,
    ExtraToken(&'i str),
    UnexpectedToken(&'i str, &'i str),
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnexpectedEOF => write!(f, "Unexpected End of File"),
            Error::ExtraToken(token) => write!(f, "Extra token: {}", token),
            Error::UnexpectedToken(actual, expected) => {
                write!(f, "Expected token '{}' but got '{}'", expected, actual)
            }
        }
    }
}

pub fn parse<S: SexprFactory>(input: &str) -> Result<S::Sexpr> {
    let mut token_stream = Tokenizer::new(input);

    let sexpr = parse_expr::<S>(&mut token_stream)?;

    if let Some(extra) = token_stream.peek_token() {
        return Err(Error::ExtraToken(extra));
    }

    Ok(sexpr)
}

fn parse_expr<'i, S: SexprFactory>(token_stream: &mut Tokenizer<'i>) -> Result<'i, S::Sexpr> {
    let token = token_stream.next().ok_or(Error::UnexpectedEOF)?;

    if token == ")" || token == "." {
        Err(Error::UnexpectedToken(token, ""))
    } else if token == "'" {
        parse_expr::<S>(token_stream).map(|x| S::quote(x))
    } else if token == "(" {
        parse_list::<S>(token_stream)
    } else if token.starts_with('"') && token.ends_with('"') {
        Ok(S::string(token.trim_matches('"')))
    } else if let Ok(x) = token.parse::<S::Integer>() {
        Ok(S::int(x))
    } else if let Ok(x) = token.parse::<S::Float>() {
        Ok(S::float(x))
    } else {
        Ok(S::symbol(token))
    }
}

fn parse_list<'i, S: SexprFactory>(token_stream: &mut Tokenizer<'i>) -> Result<'i, S::Sexpr> {
    let mut items = vec![];

    while token_stream.peek_token().ok_or(Error::UnexpectedEOF)? != ")" {
        if token_stream.peek_token().unwrap() != "." {
            items.push(parse_expr::<S>(token_stream)?);
        } else {
            token_stream.next_token();
            let car = items.pop().ok_or(Error::UnexpectedToken(".", ""))?;
            let cdr = parse_expr::<S>(token_stream)?;
            let delimiter = token_stream.next_token().ok_or(Error::UnexpectedEOF)?;
            if delimiter != ")" {
                return Err(Error::UnexpectedToken(delimiter, ")"));
            }
            let mut cdr = S::pair(car, cdr);
            while let Some(car) = items.pop() {
                cdr = S::pair(car, cdr);
            }
            return Ok(cdr);
        }
    }

    token_stream.next_token();
    Ok(S::list(items))
}

struct Tokenizer<'i> {
    input: &'i [u8],
    cursor: usize,
    current_token: Option<&'i str>,
}

impl<'i> Iterator for Tokenizer<'i> {
    type Item = &'i str;
    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}

impl<'i> Tokenizer<'i> {
    fn new(input: &'i str) -> Self {
        let input = input.as_bytes();
        let mut this = Tokenizer {
            input,
            cursor: 0,
            current_token: None,
        };
        this.skip_whitespace();
        this.next_token();
        this
    }

    fn peek_char(&self) -> Option<u8> {
        if self.cursor >= self.input.len() {
            None
        } else {
            Some(self.input[self.cursor])
        }
    }

    fn next_char(&mut self) -> Option<u8> {
        if self.cursor >= self.input.len() {
            None
        } else {
            let ch = self.input[self.cursor];
            self.cursor += 1;
            Some(ch)
        }
    }

    fn skip_whitespace(&mut self) {
        while self.peek_char().filter(u8::is_ascii_whitespace).is_some() {
            self.next_char();
        }
    }

    fn next_token(&mut self) -> Option<&'i str> {
        let token = if self.cursor >= self.input.len() {
            None
        } else {
            let begin = self.cursor;

            if self.peek_char() == Some(b'"') {
                self.next_char();
                while self.next_char()? != b'"' {}
            } else {
                while self.peek_char().filter(not(is_delimiter)).is_some() {
                    self.next_char();
                }
            }

            // yield at least one character
            if self.cursor == begin {
                self.next_char();
            }

            let end = self.cursor;

            self.skip_whitespace();

            Some(std::str::from_utf8(&self.input[begin..end]).unwrap())
        };

        std::mem::replace(&mut self.current_token, token)
    }

    fn peek_token(&self) -> Option<&'i str> {
        self.current_token
    }
}

fn is_delimiter(ch: &u8) -> bool {
    match ch {
        b'(' | b')' | b'\'' => true,
        _ => ch.is_ascii_whitespace(),
    }
}

fn not(predicate: fn(&u8) -> bool) -> impl Fn(&u8) -> bool {
    move |x| !predicate(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    enum S {
        Int(i64),
        Float(f64),
        Symbol(String),
        String(String),
        List(Vec<S>),
        Pair(Box<(S, S)>),
    }

    impl SexprFactory for S {
        type Sexpr = S;
        type Integer = i64;
        type Float = f64;

        fn int(x: i64) -> S {
            S::Int(x)
        }

        fn float(x: f64) -> Self::Sexpr {
            S::Float(x)
        }

        fn symbol(x: &str) -> Self::Sexpr {
            S::Symbol(x.to_string())
        }

        fn string(x: &str) -> Self::Sexpr {
            S::String(x.to_string())
        }

        fn list(x: Vec<Self::Sexpr>) -> Self::Sexpr {
            S::List(x)
        }

        fn pair(a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr {
            S::Pair(Box::new((a, b)))
        }
    }

    #[test]
    fn example() {
        assert_eq!(
            parse::<S>("(hello . \"world\")"),
            Ok(S::pair(S::symbol("hello"), S::string("world")))
        );
    }

    #[test]
    fn empty_input() {
        assert_eq!(parse::<S>(""), Err(Error::UnexpectedEOF))
    }

    #[test]
    fn simple_number() {
        assert_eq!(parse::<S>("42"), Ok(S::Int(42)))
    }

    #[test]
    fn ignore_trailing_whitespace() {
        assert_eq!(parse::<S>("1 "), Ok(S::Int(1)))
    }

    #[test]
    fn too_many_tokens() {
        assert_eq!(parse::<S>("1 2 3"), Err(Error::ExtraToken("2")))
    }

    #[test]
    fn empty_list() {
        assert_eq!(parse::<S>("()"), Ok(S::List(vec![])))
    }

    #[test]
    fn empty_list_with_whitespace() {
        assert_eq!(parse::<S>(" (\t)  "), Ok(S::List(vec![])))
    }

    #[test]
    fn unary_list() {
        assert_eq!(parse::<S>("(1)"), Ok(S::List(vec![S::Int(1)])))
    }

    #[test]
    fn nary_list() {
        assert_eq!(
            parse::<S>("(1 2 3)"),
            Ok(S::List(vec![S::Int(1), S::Int(2), S::Int(3)]))
        )
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            parse::<S>("((())())"),
            Ok(S::List(vec![
                S::List(vec![S::List(vec![])]),
                S::List(vec![])
            ]))
        )
    }

    #[test]
    fn floatingpoint_number() {
        assert_eq!(parse::<S>("-0.2"), Ok(S::Float(-0.2)))
    }

    #[test]
    fn symbol() {
        assert_eq!(
            parse::<S>(":foo-bar?"),
            Ok(S::Symbol(":foo-bar?".to_owned()))
        )
    }

    #[test]
    fn empty_string() {
        assert_eq!(parse::<S>("\"\""), Ok(S::String("".to_owned())))
    }

    #[test]
    fn simple_string() {
        assert_eq!(parse::<S>("\"hello\""), Ok(S::String("hello".to_owned())))
    }

    #[test]
    fn spacy_string() {
        assert_eq!(
            parse::<S>("\"hello world\""),
            Ok(S::String("hello world".to_owned()))
        )
    }

    #[test]
    fn invalid_string() {
        assert_eq!(parse::<S>("\"hello "), Err(Error::UnexpectedEOF))
    }

    #[test]
    fn pairs() {
        assert_eq!(parse::<S>("(1 . 2)"), Ok(S::pair(S::Int(1), S::Int(2))))
    }

    #[test]
    fn invalid_pairs() {
        assert_eq!(parse::<S>("(1 . )"), Err(Error::UnexpectedToken(")", "")));
        assert_eq!(parse::<S>("( . 2)"), Err(Error::UnexpectedToken(".", "")));
        assert_eq!(parse::<S>("( . )"), Err(Error::UnexpectedToken(".", "")));
    }

    #[test]
    fn improper_list() {
        assert_eq!(
            parse::<S>("(1 2 . 3)"),
            Ok(S::pair(S::Int(1), S::pair(S::Int(2), S::Int(3))))
        )
    }

    #[test]
    fn quoted_symbol() {
        assert_eq!(
            parse::<S>("'foo"),
            Ok(S::list(vec![S::symbol("quote"), S::symbol("foo")]))
        )
    }

    #[test]
    fn quoted_list() {
        assert_eq!(
            parse::<S>("'()"),
            Ok(S::list(vec![S::symbol("quote"), S::list(vec![])]))
        )
    }
}
