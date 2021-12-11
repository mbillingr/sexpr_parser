# sexpr_parser
Generic S-Expression parser.

Need to parse an S-Expression string into your own data structure? No problem!
Just implement the `SexprFactory` trait and call the `parse` function.

## Example

Let's assume `S` is *your* data structure. Here is how you parse it:

```rust
use sexpr_parser::parse;

assert_eq!(
    parse::<S>("(hello . \"world\")"),
    Ok(S::pair(S::symbol("hello"), S::string("world")))
);
```

To make this work, implement the `SexprFactory` trait for `S`:

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
        let mut tail = S::Nil;
        for item in x.into_iter().rev() {
            tail = S::pair(item, tail)
        }
        tail
    }

    fn pair(a: Self::Sexpr, b: Self::Sexpr) -> Self::Sexpr {
        S::Pair(Box::new((a, b)))
    }
}
```

If you use a third-party data structure instead of your own `S` you can't implement the trait on this type, but you can do this:

```rust
use cool_3rd_party_crate::ForeignSexpr;

struct SF;  // you totally own the factory type

impl SexprFactory for SF {
    type Sexpr = ForeignSexpr;
    // ...
}
```
