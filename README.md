# sexpr_parser
Generic S-Expression parser.

Need to parse an S-Expression string into your own data structure? No problem!
Just implement the `SexprFactory` trait and call the `parse` function.

## Example

Let's assume `S` is *your* data structure and `SF` is a type that known how to construct values of `S`.
Here is how you parse it:

```rust
use sexpr_parser::{parse, Parser};

assert_eq!(
    SF.parse("(hello . \"world\")"),
    Ok(SF.pair(SF.symbol("hello"), SF.string("world")))
);
```

To make this work, implement the `SexprFactory` trait for `SF`:

```rust

use sexpr_parser::SexprFactory;

/// Your amazing S-expression data structure
#[derive(Debug, PartialEq)]
enum S {
    Nil,
    Int(i64),
    Float(f64),
    Symbol(String),
    String(String),
    Pair(Box<(S, S)>),
}

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
        let mut tail = S::Nil;
        for item in x.into_iter().rev() {
            tail = S::pair(item, tail)
        }
        tail
    }

    fn pair(&mut self, a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr {
        S::Pair(Box::new((a, b)))
    }
}
```

Not that you can even use a third-party data structure instead of your own `S`.
All you need to do is define and implement a factory structure.
