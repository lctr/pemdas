# Pemdas
A REPL-like utility that helps to visualize how expressions parse
according to (custom or preset) operator precedences and
associativities.

The name *PEMDAS* comes from the acronym commonly taught in early
American algebra courses as a mnemonic for remembering the [order of
operations](https://en.wikipedia.org/wiki/Order_of_operations),
providing an easy reminder for why an expression like
```math
a + b * c ^ e - f / g
```
is parsed as
```math
a + (b * (c ^ e)) - (f / g)
```
by the average calculator, and can be defined in the REPL by inputting
```haskell
infixl 6 +, -
infixl 7 *, /
infixr 8 ^
```

Modeled after the Haskell programming language, each REPL session
allows for *fixity declarations*, which allow the user to not only
define custom operators, but also how such operators would parse in an
expression. These custom session-defined operators may then be used in
arbitrary expressions, which are parsed and pretty printed for the
user to see how infix expressions may group.

The syntax for declaring fixities is nearly identical to that of
*Haskell*'s -- though the *lexical* syntax is slightly modified -- and
can be found at the bottom of this README.

# Features
## Local fixity declarations
`let` expressions allow for locally scoped fixity declarations. Since
*Pemdas* is not an interpreter (it is effectively just an interactive
pretty printer), only fixity declarations are allowed after a `let`
and before the keyword `in`. Additionally, declaring multiple locally
scoped fixities requires nested `let` expressions.

Thus, to locally redefine `+` as left-associative with precedence `4`
and `?` as right-associative with precedence `6`, we'd write `let
infixl 4 + in let infixr 6 ? in a + b ? c + d`.

## Decorative syntax nodes
Support for lexing and parsing literals (such as `'x'`, `"foo"`, `55`,
and `"\u+7FA"`) plays a purely aesthetic role as no computation or
interpretation is actually done. Unicode escapes are accepted, thus
`"\U+0041"`, `"\u+41"`, `"\u41"` and `"A"` will all print `"A"`.

Likewise, `lambda`, `tuple` and (imple) `list` expressions are also
supported, allowing for expressions like `(a, b)` and `[x, 1, (\f -> f
x) id]` to be entered and pretty printed.

## Presets
Predefined fixities from the Haskell Prelude, along with standard
arithmetic operator fixities, are provided and may be loaded in a REPL
session by `:load --prelude` and `:load --math`, respectively.
Alternatively, files may be loaded in session with `:load <path>`,
where `<path>` is the filepath of the desired file.


## Syntax reference
### Lexical syntax
There is a slight stylistic difference in *Pemdas*'s lexical syntax:
* Identifiers -- beginning with either `_`, an uppercase or lowercase
  alphabetic character -- consisting of more than one character may be
  promoted to operators, rendering `` `elem` `` and `'elem` lexically
  identical, but *not* `` `f` `` and `'f'` (since the latter would lex
  as a character literal)
  * for example, *Pemdas* will parse the expressions
    ```haskell
    x 'elem y
    ```
    and
    ```haskell
    e `elem` y
    ```
    identically.
  * While no *actual* expression evaluation is performed, I wanted to
    allow for the possibility of including literals in expressions, so
    it is necessary to use surrounding backticks when promoting
    single-character identifiers.
* Infixes may be treated as function identifiers by surrounding them in
  parentheses, e.g., `a + b` parses as a binary (infix) expression,
  while `(+) a b` parses as a function application.
* Both infixes and identifiers may end in a sequence of any
  combination of superscript/subscript digits, superscript/subscript
  parentheses or superscript/subscript
* Line comments by default begin with `~~ `, where the double tildes
  `~~` *must* be followd be a non-operator character (infixes
  beginning with `~~` followed by another operator character, such as
  `~~+`, are read as infixes).

### Formal syntax
A fixity declaration consists of an *associativity* keyword (`infixl`, `infixr` or
`infix`) followed by an optional *precedence* value (a digit between `0`
and `9`, inclusive) and a comma-separated (non-empty) list of
*infixes*.

If no precedence value is given, then a default value of `9` is
assumed.

The rules below (inspired by the syntax reference from the [Haskell 98
Report]) are described in [EBNF] form and use the following
shorthand:
| Shorthand | Description
|-----------|----------------------------------------------------------
| `"p"`     | the occurrence of the terminal string `p`
| `(p)`     | the grouping of compound rules as a single rule `p`
| `[p]`     | the production `p` is optional
| `{p}`     | the production `p` repeated 0 or more times
| `p+`      | the production `p` repeated atleast once
| `p1 , p2` | the concatenation of `p1` followed by `p2`
| `;`       | the end of a production rule
| `p1 \| p2`| the (ordered) choice of productions `p1` or `p2`
| `p1 \ p2` | the production of elements in `p1` excluding elements from `p2`

```ebnf
fixity  = assoc , prec , infixes ;
assoc   = "infixl" | "infixr" | "infix" ;
prec    = [digit] ;
digit   = "0" | "1" | "2" | "3" | "4"
        | "5" | "6" | "7" | "8" | "9" ;
infixes = infix , {"," infix} ;
infix   = "`" ident "`"
        |  (opchars \ "~~"), { trails } ;
opchars = opchar , { opchar };
opchar  = "!" | "#" | "$" | "%" | "&"
        | "*" | "+" | "." | "/" | "<"
        | "=" | ">" | "?" | "@" | "\​"
        | "^" | "|" | "-" | "~";
trails  = supscr | subscr;
supscr  = "⁰" | "¹" | "²" | "³" | "⁴"
        | "⁵" | "⁶" | "⁷" | "⁸" | "⁹"
        | "⁽" | "⁾" | "⁺" | "⁻" ;
subscr  = "₀" | "₁" | "₂" | "₃" | "₄"
        | "₅" | "₆" | "₇" | "₈" | "₉"
        | "₍" | "₎" | "₊" | "₋";

ident   = lower, { upper | lower | digit | "_" }, trails?
        | "_"+, { upper | lower | digit | "_" }, trails?
        | upper, { upper | lower | digit | "_" }, trails?
        ;

lower   = <any lowercase alphabetic character>;
upper   = <any uppercase alphabetic character>;

expr    = "\​", (pat)+, "->", expr          (* lambda *)
        | "let", fixity, "in", expr        (* local fixity *)
        | fexp                             (* function expr *)
        ;
fexp    = [fexp] aexp
        ;
aexp    = ident
        | literal
        | "(", infix, ")"
        | "(", expr, ")"                   (* grouped expression *)
        | "(", expr, ("," , expr)+, ")"    (* tuple *)
        | "[", expr, { ",", expr }, "]"    (* list *)
        | expr infix expr                  (* binary expression *)
        ;
```

[EBNF]:
    https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form
[Haskell 98 Report]:
    https://www.haskell.org/onlinereport/syntax-iso.html#sect9