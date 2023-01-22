use std::fmt;

use crate::text::symbol::Symbol;

pub type Row = u32;
pub type Col = u32;
pub type BytePos = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Loc {
    pub line: Row,
    pub col: Col,
    pub pos: BytePos,
}

impl Default for Loc {
    fn default() -> Self {
        Self {
            line: 1,
            col: 1,
            pos: 0,
        }
    }
}

impl Loc {
    pub fn new(line: Row, col: Col, pos: BytePos) -> Self {
        Self { line, col, pos }
    }

    pub fn write_lncol(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", &self.line, &self.col)
    }
}

impl std::fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]:{}:{}", self.pos, self.line, self.col)
    }
}

impl From<(Row, Col, BytePos)> for Loc {
    fn from((line, col, pos): (Row, Col, BytePos)) -> Self {
        Self::new(line, col, pos)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub lo: BytePos,
    pub hi: BytePos,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.lo, self.hi)
    }
}

impl std::ops::Index<Span> for str {
    type Output = str;

    fn index(&self, index: Span) -> &Self::Output {
        &self[index.lo..index.hi]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct LocSpan {
    pub lo: Loc,
    pub hi: Loc,
}

impl LocSpan {
    pub const fn new(lo: Loc, hi: Loc) -> Self {
        Self { lo, hi }
    }

    pub fn span(&self) -> Span {
        Span {
            lo: self.lo.pos,
            hi: self.hi.pos,
        }
    }

    pub fn lines(&self) -> usize {
        self.hi.line.abs_diff(self.lo.line) as usize
    }

    pub fn is_empty(&self) -> bool {
        self.lo == self.hi
    }
}

impl From<(Loc, Loc)> for LocSpan {
    fn from((lo, hi): (Loc, Loc)) -> Self {
        Self { lo, hi }
    }
}

impl std::ops::Index<LocSpan> for str {
    type Output = str;

    fn index(&self, index: LocSpan) -> &Self::Output {
        &self[index.lo.pos..index.hi.pos]
    }
}

impl fmt::Display for LocSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.lo, self.hi)
    }
}

pub type IntRep = usize;
pub type FracRep = Option<u32>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct ExpRep(isize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Float {
    pub int: IntRep,
    pub frac: FracRep,
    pub exp: ExpRep,
}

impl Float {
    pub fn new(int: IntRep, frac: FracRep, exp: ExpRep) -> Self {
        Self { int, frac, exp }
    }

    pub fn write_fmt_str(&self, w: &mut impl fmt::Write) -> fmt::Result {
        let Self { int, frac, exp } = self;
        write!(w, "{int}")?;
        if let Some(frac) = frac {
            write!(w, ".{frac}")?;
        }
        let ExpRep(exp) = exp;
        if *exp != 0 {
            write!(w, "{exp}")?;
        }
        Ok(())
    }

    pub fn string(&self) -> String {
        let Self { int, frac, exp } = self;
        let mut buf = String::new();
        buf.push_str(&*format!("{int}"));
        if let Some(frac) = frac {
            buf.push_str(&*format!(".{frac}"))
        }
        let ExpRep(exp) = exp;
        if *exp != 0 {
            buf.push_str(&*format!("{exp}"));
        }
        buf
    }

    pub fn to_f64(self) -> f64 {
        self.string().parse::<f64>().unwrap()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Char(char),
    Str(Symbol),
    Int(IntRep),
    Frac(Float),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Char(c) => write!(f, "{c:?}"),
            Literal::Str(s) => write!(f, "{:?}", s.as_str()),
            Literal::Int(n) => write!(f, "{n:?}"),
            Literal::Frac(frac) => frac.write_fmt_str(f),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Token {
    ParenL,
    ParenR,
    BrackL,
    BrackR,
    CurlyL,
    CurlyR,
    Comma,
    Semi,
    Underscore,
    Lambda,
    Arrow,
    Dash,
    Dot,
    At,
    InfixL,
    InfixR,
    Infix,
    Let,
    In,
    Upper(Symbol),
    Lower(Symbol),
    Affix(Symbol, bool),
    Lit(Literal),
    Eof,
    Error(LexError),
}

macro_rules! F {
    ($f:ident$(::$fs:ident)* .) => {
        |g| |x| $f$(::$fs)*(g(x))
    };
    (
        $f:ident$(::$fs:ident)*
        . $g:ident$(::$gs:ident)*
        $(. $h:ident$(::$hs:ident)*)*
    ) => {{
        let fg = |x| $f$(::$fs)*($g$(::$gs)*(x));
        $(let fg = |x| fg($h$(::$hs)*(x));)*
        fg
    }};
}

impl Token {
    #[allow(non_upper_case_globals)]
    pub const Char: fn(char) -> Token = F!(Token::Lit . Literal::Char);
    #[allow(non_upper_case_globals)]
    pub const Int: fn(IntRep) -> Token = F!(Token::Lit . Literal::Int);
    #[allow(non_upper_case_globals)]
    pub const Str: fn(Symbol) -> Token = F!(Token::Lit . Literal::Str);

    pub const fn is_eof(&self) -> bool {
        matches!(self, Self::Eof)
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        macro_rules! mk {
            ($f:ident) => {
                macro_rules! S {
                    (;$id:ident) => {
                        write!($f, "{}", stringify!($id))
                    };
                    (;^$s:ident $m:ident) => {
                        write!($f, "'{}", $s.$m())
                    };
                    (;$t:tt) => {
                        write!($f, "{}", stringify!($t))
                    };
                    ($e:expr) => {
                        write!($f, "{}", $e)
                    };
                    ($s:ident $m:ident) => {
                        write!($f, "{}", $s.$m())
                    };
                    ($s:ident $m:ident ()) => {
                        $s.$m($f)
                    };
                    ($t:tt) => {
                        write!($f, "{}", stringify!($t))
                    };
                }
            };
        }
        mk!(f);
        match self {
            Token::ParenL => S!('('),
            Token::ParenR => S!(')'),
            Token::BrackL => S!('['),
            Token::BrackR => S!(']'),
            Token::CurlyL => S!('{'),
            Token::CurlyR => S!('}'),
            Token::Comma => S!(,),
            Token::Semi => S!(;),
            Token::Underscore => S!(_),
            Token::Dash => S!(;-),
            Token::Dot => S!(;.),
            Token::At => S!(;@),
            Token::Lambda => S!('\\'),
            Token::Arrow => S!(->),
            Token::InfixL => S!(;infixl),
            Token::InfixR => S!(;infixr),
            Token::Infix => S!(;infix),
            Token::Let => S!(;let),
            Token::In => S!(;in),
            Token::Upper(s) | Token::Lower(s) => S!(s as_str),
            Token::Affix(s, promoted) => {
                if *promoted {
                    S!(;^s as_str)
                } else {
                    S!(s as_str)
                }
            }
            Token::Lit(lit) => S!(lit fmt ()),
            Token::Eof => S!('\0'),
            Token::Error(e) => S!(e fmt ()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LexError {
    EmptyChar(Loc, Loc),
    InvalidEscape(char, Loc, Loc),
    InvalidInt(Loc, IntError),
    InvalidPromotedInfix(Loc, Symbol),
    UnterminatedChar(Loc, Loc),
    UnterminatedString(Loc),
    UnterminatedComment(Loc, Loc),
    InvalidUnicode(Loc, CodePointError),
    Unknown,
}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexError::EmptyChar(..) => todo!(),
            LexError::InvalidEscape(c, ..) => {
                write!(f, "the sequence `\\{c}` is not a valid character escape")
            }
            LexError::InvalidInt(loc, err) => {
                let (a, b) = err.text();
                write!(f, "{a}at {loc}{b}")
            }
            LexError::InvalidPromotedInfix(loc, sym) => {
                write!(
                    f,
                    "invalid identifier `{sym}` in operator promotion at {loc}"
                )
            }
            LexError::UnterminatedChar(start, _end) => {
                write!(f, "unterminated character literal starting at {start}")
            }
            LexError::UnterminatedString(start) => {
                write!(f, "unterminated string literal starting at {start}")
            }
            LexError::UnterminatedComment(start, _end) => write!(
                f,
                "block comment starting at {}:{} was not terminated",
                start.line, start.col
            ),
            LexError::InvalidUnicode(loc, kind) => match kind {
                CodePointError::Empty => {
                    write!(f, "expected codepoint for unicode escape at {loc}")
                }
                CodePointError::BadConnector(ch) => {
                    write!(f, "invalid character `{ch}` found following unicode escape `\\u`; expected `+` or hexadecimal after")
                }
                CodePointError::TooLong(s) => {
                    write!(
                        f,
                        "unicode escape `{s}` is more than the maximum length of 6 hex digits"
                    )
                }
                CodePointError::NotInCharRange(sym, int) => {
                    write!(f, "the integer `{sym}` ({int}) is out of the range for valid character values")
                }
                #[allow(unreachable_patterns)]
                _ => todo!(),
            },
            LexError::Unknown => write!(f, "unknown lexer error"),
        }
    }
}

#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CodePointError {
    Empty,
    BadConnector(char),
    TooLong(Symbol),
    NotInCharRange(Symbol, u32),
}

// impl fmt::Display for UnicodeFail {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         todo!()
//     }
// }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntError {
    /// Indicates an unterminated binary, octal, or
    /// hexadecimal integer, i.e., unexpectedly ending after the
    /// prefix
    Incomplete,
    InvalidDigit,
    PosOverflow,
    NegOverflow,
}

impl From<std::num::ParseIntError> for IntError {
    fn from(err: std::num::ParseIntError) -> Self {
        match err.kind() {
            std::num::IntErrorKind::Empty => Self::Incomplete,
            std::num::IntErrorKind::InvalidDigit => Self::InvalidDigit,
            std::num::IntErrorKind::PosOverflow => Self::PosOverflow,
            std::num::IntErrorKind::NegOverflow => Self::NegOverflow,
            std::num::IntErrorKind::Zero => {
                unreachable!("the type of integer being parsed into is not a non-zero type")
            }
            _ => unreachable!("std::num::IntErrorKind is non-exhaustive"),
        }
    }
}

impl IntError {
    pub fn text(&self) -> (&str, &str) {
        match self {
            IntError::Incomplete => (
                "no digits found after the numeric prefix ",
                " while parsing into an integer",
            ),
            IntError::InvalidDigit => (
                "invalid digit found in the token ",
                " while parsing into an integer",
            ),
            IntError::PosOverflow => (
                "the token ",
                " is too large to be correctly parsed into an integer",
            ),
            IntError::NegOverflow => (
                "the token ",
                " is too small to be correctly parsed into an integer",
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[default_variant::default(Eof)]
pub enum Char {
    Eof,
    Chr(char),
}

impl std::ops::Deref for Char {
    type Target = char;

    fn deref(&self) -> &Self::Target {
        match self {
            Char::Eof => &'\0',
            Char::Chr(c) => c,
        }
    }
}

impl PartialEq<char> for Char {
    fn eq(&self, other: &char) -> bool {
        &**self == other
    }
}

impl PartialEq<Char> for char {
    fn eq(&self, other: &Char) -> bool {
        self == &**other
    }
}

impl PartialEq<&char> for Char {
    fn eq(&self, other: &&char) -> bool {
        &**self == *other
    }
}

impl PartialEq<Char> for &char {
    fn eq(&self, other: &Char) -> bool {
        *self == &**other
    }
}

impl From<Option<char>> for Char {
    fn from(value: Option<char>) -> Self {
        if let Some(c) = value {
            Char::Chr(c)
        } else {
            Char::Eof
        }
    }
}

impl Char {
    pub const fn is_eof(&self) -> bool {
        matches!(self, Self::Eof)
    }

    #[inline]
    pub const fn len_utf8(self) -> usize {
        match self {
            Char::Eof => '\0',
            Char::Chr(c) => c,
        }
        .len_utf8()
    }

    pub fn as_str<'a>(&'a self) -> &'a str {
        if self.is_eof() {
            ""
        } else {
            let mut buf = vec![0; self.len_utf8()];
            self.encode_utf8(&mut buf[..]);
            unsafe { std::mem::transmute::<_, &'a str>(&buf[..]) }
        }
    }
}
