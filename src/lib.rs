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
    fn int(&mut self, x: Self::Integer) -> Self::Sexpr;

    /// construct a floating point value
    fn float(&mut self, x: Self::Float) -> Self::Sexpr;

    /// construct a symbol
    fn symbol(&mut self, x: &str) -> Self::Sexpr;

    /// construct a string
    fn string(&mut self, x: &str) -> Self::Sexpr;

    /// construct a list
    fn list(&mut self, x: Vec<Self::Sexpr>) -> Self::Sexpr;

    /// construct a pair
    fn pair(&mut self, a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr;

    /// construct a quotation
    fn quote(&mut self, x: Self::Sexpr) -> Self::Sexpr {
        let q = self.symbol("quote");
        self.list(vec![q, x])
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

pub trait Parser: SexprFactory {
    fn parse<'i>(&mut self, input: &'i str) -> Result<'i, Self::Sexpr> {
        let mut token_stream = Tokenizer::new(input);

        let sexpr = parse_expr(self, &mut token_stream)?;

        if let Some(extra) = token_stream.peek_token() {
            return Err(Error::ExtraToken(extra));
        }

        Ok(sexpr)
    }
}

impl<T: SexprFactory> Parser for T {}

pub fn parse<S: Default + Parser>(input: &str) -> Result<S::Sexpr> {
    S::default().parse(input)
}

fn parse_expr<'i, S: SexprFactory + ?Sized>(
    factory: &mut S,
    token_stream: &mut Tokenizer<'i>,
) -> Result<'i, S::Sexpr> {
    let token = token_stream.next().ok_or(Error::UnexpectedEOF)?;

    if token == ")" || token == "." {
        Err(Error::UnexpectedToken(token, ""))
    } else if token == "'" {
        parse_expr(factory, token_stream).map(|x| factory.quote(x))
    } else if token == "(" {
        parse_list(factory, token_stream)
    } else if token.starts_with('"') && token.ends_with('"') {
        Ok(factory.string(token.trim_matches('"')))
    } else if let Ok(x) = token.parse::<S::Integer>() {
        Ok(factory.int(x))
    } else if let Ok(x) = token.parse::<S::Float>() {
        Ok(factory.float(x))
    } else {
        Ok(factory.symbol(token))
    }
}

fn parse_list<'i, S: SexprFactory + ?Sized>(
    factory: &mut S,
    token_stream: &mut Tokenizer<'i>,
) -> Result<'i, S::Sexpr> {
    let mut items = vec![];

    while token_stream.peek_token().ok_or(Error::UnexpectedEOF)? != ")" {
        if token_stream.peek_token().unwrap() != "." {
            items.push(parse_expr(factory, token_stream)?);
        } else {
            token_stream.next_token();
            let car = items.pop().ok_or(Error::UnexpectedToken(".", ""))?;
            let cdr = parse_expr(factory, token_stream)?;
            let delimiter = token_stream.next_token().ok_or(Error::UnexpectedEOF)?;
            if delimiter != ")" {
                return Err(Error::UnexpectedToken(delimiter, ")"));
            }
            let mut cdr = factory.pair(car, cdr);
            while let Some(car) = items.pop() {
                cdr = factory.pair(car, cdr);
            }
            return Ok(cdr);
        }
    }

    token_stream.next_token();
    Ok(factory.list(items))
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

    #[derive(Default)]
    struct SF;

    impl SexprFactory for SF {
        type Sexpr = S;
        type Integer = i64;
        type Float = f64;

        fn int(&mut self, x: i64) -> S {
            S::Int(x)
        }

        fn float(&mut self, x: f64) -> Self::Sexpr {
            S::Float(x)
        }

        fn symbol(&mut self, x: &str) -> Self::Sexpr {
            S::Symbol(x.to_string())
        }

        fn string(&mut self, x: &str) -> Self::Sexpr {
            S::String(x.to_string())
        }

        fn list(&mut self, x: Vec<Self::Sexpr>) -> Self::Sexpr {
            S::List(x)
        }

        fn pair(&mut self, a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr {
            S::Pair(Box::new((a, b)))
        }
    }

    #[test]
    fn example() {
        assert_eq!(
            SF.parse("(hello . \"world\")"),
            Ok(SF.pair(SF.symbol("hello"), SF.string("world")))
        );
    }

    #[test]
    fn empty_input() {
        assert_eq!(parse::<SF>(""), Err(Error::UnexpectedEOF))
    }

    #[test]
    fn simple_number() {
        assert_eq!(parse::<SF>("42"), Ok(S::Int(42)))
    }

    #[test]
    fn ignore_trailing_whitespace() {
        assert_eq!(parse::<SF>("1 "), Ok(S::Int(1)))
    }

    #[test]
    fn too_many_tokens() {
        assert_eq!(parse::<SF>("1 2 3"), Err(Error::ExtraToken("2")))
    }

    #[test]
    fn empty_list() {
        assert_eq!(parse::<SF>("()"), Ok(S::List(vec![])))
    }

    #[test]
    fn empty_list_with_whitespace() {
        assert_eq!(parse::<SF>(" (\t)  "), Ok(S::List(vec![])))
    }

    #[test]
    fn unary_list() {
        assert_eq!(parse::<SF>("(1)"), Ok(S::List(vec![S::Int(1)])))
    }

    #[test]
    fn nary_list() {
        assert_eq!(
            parse::<SF>("(1 2 3)"),
            Ok(S::List(vec![S::Int(1), S::Int(2), S::Int(3)]))
        )
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            parse::<SF>("((())())"),
            Ok(S::List(vec![
                S::List(vec![S::List(vec![])]),
                S::List(vec![])
            ]))
        )
    }

    #[test]
    fn floatingpoint_number() {
        assert_eq!(parse::<SF>("-0.2"), Ok(S::Float(-0.2)))
    }

    #[test]
    fn symbol() {
        assert_eq!(
            parse::<SF>(":foo-bar?"),
            Ok(S::Symbol(":foo-bar?".to_owned()))
        )
    }

    #[test]
    fn empty_string() {
        assert_eq!(parse::<SF>("\"\""), Ok(S::String("".to_owned())))
    }

    #[test]
    fn simple_string() {
        assert_eq!(parse::<SF>("\"hello\""), Ok(S::String("hello".to_owned())))
    }

    #[test]
    fn spacy_string() {
        assert_eq!(
            parse::<SF>("\"hello world\""),
            Ok(S::String("hello world".to_owned()))
        )
    }

    #[test]
    fn invalid_string() {
        assert_eq!(parse::<SF>("\"hello "), Err(Error::UnexpectedEOF))
    }

    #[test]
    fn pairs() {
        assert_eq!(parse::<SF>("(1 . 2)"), Ok(SF.pair(S::Int(1), S::Int(2))))
    }

    #[test]
    fn invalid_pairs() {
        assert_eq!(parse::<SF>("(1 . )"), Err(Error::UnexpectedToken(")", "")));
        assert_eq!(parse::<SF>("( . 2)"), Err(Error::UnexpectedToken(".", "")));
        assert_eq!(parse::<SF>("( . )"), Err(Error::UnexpectedToken(".", "")));
    }

    #[test]
    fn improper_list() {
        assert_eq!(
            parse::<SF>("(1 2 . 3)"),
            Ok(SF.pair(S::Int(1), SF.pair(S::Int(2), S::Int(3))))
        )
    }

    #[test]
    fn quoted_symbol() {
        assert_eq!(
            parse::<SF>("'foo"),
            Ok(SF.list(vec![SF.symbol("quote"), SF.symbol("foo")]))
        )
    }

    #[test]
    fn quoted_list() {
        assert_eq!(
            parse::<SF>("'()"),
            Ok(SF.list(vec![SF.symbol("quote"), SF.list(vec![])]))
        )
    }

    #[test]
    fn stateful_factory() {
        #[derive(Debug, PartialEq)]
        enum S<'a> {
            Nil,
            Int(i64),
            Pair(&'a (S<'a>, S<'a>)),
        }

        struct Factory<'a> {
            /// support a fixed number of preallocated pairs
            pairs: Box<[(S<'a>, S<'a>); 2]>,
            next_free_pair: usize,
        }

        impl Factory<'_> {
            pub fn new() -> Self {
                Factory {
                    pairs: Box::new([(S::Nil, S::Nil), (S::Nil, S::Nil)]),
                    next_free_pair: 0,
                }
            }
        }

        impl<'a> SexprFactory for Factory<'a> {
            type Sexpr = S<'a>;
            type Integer = i64;
            type Float = f64;

            fn int(&mut self, x: i64) -> Self::Sexpr {
                S::Int(x)
            }

            fn float(&mut self, _: f64) -> Self::Sexpr {
                unimplemented!()
            }

            fn symbol(&mut self, _: &str) -> Self::Sexpr {
                unimplemented!()
            }

            fn string(&mut self, _: &str) -> Self::Sexpr {
                unimplemented!()
            }

            fn list(&mut self, x: Vec<Self::Sexpr>) -> Self::Sexpr {
                let mut tail = S::Nil;
                for item in x.into_iter().rev() {
                    tail = self.pair(item, tail)
                }
                tail
            }

            fn pair(&mut self, a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr {
                if self.next_free_pair >= self.pairs.len() {
                    panic!("out of storage space")
                }
                let k = self.next_free_pair;
                self.next_free_pair += 1;
                self.pairs[k] = (a, b);

                // Cast through raw pointer, so that the borrow checker forgets
                // the pair is a part of the pairs array.
                // This should be safe because the pairs in the array do not overlap.
                let p = unsafe { &mut *(&mut self.pairs[k] as *mut _) };

                S::Pair(p)
            }
        }

        let mut fact = Factory::new();

        let x = fact.parse("(1 2)");
        assert_eq!(x, Ok(S::Pair(&(S::Int(1), S::Pair(&(S::Int(2), S::Nil))))))
    }
}
