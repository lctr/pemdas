use crate::text::{
    grapheme::{self, Match},
    symbol::Symbol,
};

use super::token::{
    BytePos, Char, CodePointError, Col, LexError, Literal, Loc, LocSpan, Row, Token,
};

type Chars<'t> = std::iter::Peekable<std::str::Chars<'t>>;

#[derive(Clone, Debug)]
pub struct Lexer<'t> {
    src: &'t str,
    chars: Chars<'t>,
    curr: Option<Token>,
    line: Row,
    col: Col,
    pos: BytePos,
    prev_loc: Loc,
}

const EOF: char = '\0';

impl<'t> Lexer<'t> {
    pub fn new(src: &'t str) -> Self {
        let mut this = Self {
            src,
            chars: src.chars().peekable(),
            curr: None,
            line: 1,
            col: 1,
            pos: 0,
            prev_loc: Loc::default(),
        };
        this.eat_whitespace();
        this
    }

    pub fn is_done(&mut self) -> bool {
        self.chars.peek().is_none()
    }

    pub fn prev_loc(&self) -> Loc {
        self.prev_loc
    }

    pub fn curr_loc(&self) -> Loc {
        Loc {
            line: self.line as u32,
            col: self.col as u32,
            pos: self.pos,
        }
    }

    pub fn loc_span(&self) -> LocSpan {
        LocSpan {
            lo: self.prev_loc(),
            hi: self.curr_loc(),
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if self.curr.is_none() {
            // let loc = self.curr_loc();
            match self.lex() {
                Token::Eof => (),
                t => {
                    self.curr = Some(t);
                }
            };
            // self.prev_loc = loc;
        }
        self.curr.as_ref()
    }

    fn peek_char(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    #[inline]
    fn current_char(&mut self) -> char {
        self.peek_char().copied().unwrap_or_else(|| EOF)
    }

    fn on_char(&mut self, ch: impl Match<char>) -> bool {
        matches!(self.peek_char(), Some(c) if ch.check(c))
    }

    fn bump_char(&mut self) -> Char {
        if let Some(c) = self.chars.next() {
            self.pos += c.len_utf8();
            if c == '\n' {
                self.col = 1;
                self.line += 1;
                if self.on_char('\r') {
                    self.chars.next();
                }
            } else {
                self.col += 1;
            }
            Char::Chr(c)
        } else {
            Char::Eof
        }
    }

    pub fn bump(&mut self) -> Token {
        match self.curr.take() {
            Some(tok) => tok,
            None => Token::Eof,
        }
    }

    #[inline]
    fn bump_and(&mut self, token: Token) -> Token {
        self.bump_char();
        token
    }

    fn eat_while(&mut self, mut f: impl FnMut(char) -> bool) -> (usize, usize) {
        let start = self.pos;
        while matches!(self.peek_char(), Some(c) if f(*c)) {
            self.bump_char();
        }
        (start, self.pos)
    }

    fn eat_whitespace(&mut self) {
        self.eat_while(char::is_whitespace);
        self.prev_loc = self.curr_loc();
    }

    fn lex(&mut self) -> Token {
        self.eat_whitespace();
        self.prev_loc = self.curr_loc();
        if let Some(c) = self.peek_char() {
            match c {
                &';' => self.bump_and(Token::Semi),
                &'\'' => self.char(),
                &'"' => self.string(),
                c if c.is_digit(10) => self.number(),
                &'`' => {
                    self.bump_char();
                    let loc = self.curr_loc();
                    if self
                        .peek_char()
                        .map(|c| grapheme::is_ident_start(*c))
                        .unwrap_or_else(|| false)
                    {
                        self.promoted_operator()
                    } else {
                        let (start, end) = self.eat_while(|c| c != '`');
                        if self.peek_char().map(|c| *c == '`').unwrap_or_else(|| false) {
                            self.bump_char();
                        }
                        Token::Error(LexError::InvalidPromotedInfix(
                            loc,
                            Symbol::intern(&self.src[start..end]),
                        ))
                    }
                }
                &c if grapheme::is_ident_start(c) => self.ident(c),
                &'(' => self.bump_and(Token::ParenL),
                &')' => self.bump_and(Token::ParenR),
                &'[' => self.bump_and(Token::BrackL),
                &']' => self.bump_and(Token::BrackR),
                &'{' => self.bump_and(Token::CurlyL),
                &'}' => self.bump_and(Token::CurlyR),
                &',' => self.bump_and(Token::Comma),
                c if grapheme::is_infix_char(*c) => self.operator(),
                _ => Token::Error(LexError::Unknown),
            }
        } else {
            Token::Eof
        }
    }

    fn eat_with_trailing(&mut self, f: impl FnMut(char) -> bool) -> (usize, usize) {
        let (start, _) = self.eat_while(f);
        let (_, end) = self.eat_while(grapheme::is_trailing);
        (start, end)
    }

    fn number(&mut self) -> Token {
        let loc = self.prev_loc();
        let (start, end) = self.eat_while(|c| c.is_digit(10));
        match self.src[start..end].parse() {
            Ok(n) => Token::Int(n),
            Err(e) => Token::Error(LexError::InvalidInt(loc, e.into())),
        }
    }

    #[inline]
    fn operator(&mut self) -> Token {
        let start = self.pos;
        let (_, end) = self.eat_with_trailing(grapheme::is_infix_char);
        match &self.src[start..end] {
            "~" => {
                if self.on_char('{') {
                    self.bump_char();
                    if let Some(err) = self.block_comment() {
                        Token::Error(err)
                    } else {
                        self.lex()
                    }
                } else {
                    Token::Affix(Symbol::intern("~"), false)
                }
            }
            "~~" => {
                self.line_comment();
                self.lex()
            }
            "\\" | "λ" => Token::Lambda,
            "-" => Token::Dash,
            "->" | "→" | "⟶" | "↦" | "⟼" => Token::Arrow,
            "@" => Token::At,
            s => Token::Affix(Symbol::intern(s), false),
        }
    }

    /// Lexes an idntifier surrounded with backticks as an operator.
    /// Note that prefixing a valid identifier with an apostrophe is
    /// also supported (and how a promoted operator is reported, since
    /// quoted text is surrounded by backticks in error reporting).
    ///
    /// Support for surrounded backticks is primarily for
    /// compatibility with Haskell.
    fn promoted_operator(&mut self) -> Token {
        let loc = self.curr_loc();
        let start = self.pos;
        // we already confirmed the first character is a valid
        // start
        self.bump_char();
        let (_, end) = self.eat_with_trailing(grapheme::is_ident_char);
        let sym = Symbol::intern(&self.src[start..end]);
        if self.on_char('`') {
            self.bump_char();
            Token::Affix(sym, true)
        } else {
            Token::Error(LexError::InvalidPromotedInfix(loc, sym))
        }
    }

    fn ident(&mut self, c: char) -> Token {
        let (start, end) = self.eat_with_trailing(grapheme::is_ident_char);
        match &self.src[start..end] {
            "_" => Token::Underscore,
            "infixl" => Token::InfixL,
            "infixr" => Token::InfixR,
            "infix" => Token::Infix,
            "let" => Token::Let,
            "in" => Token::In,
            s => identifier(c)(s),
        }
    }

    fn char(&mut self) -> Token {
        let _start = self.pos;
        let loc = self.prev_loc();
        // skip first apostrophe
        self.bump_char();
        // let init = self.pos;
        match self.current_char() {
            // empty char, bad
            '\'' => {
                self.bump_char();
                Token::Error(LexError::EmptyChar(loc, self.prev_loc()))
            }
            // escaped char
            '\\' => {
                self.bump_char();
                match self.peek_char() {
                    Some('u' | 'U') => {
                        self.bump_char();
                        let is_hex: fn(char) -> bool = |c| c.is_ascii_hexdigit();
                        if self.on_char('+') {
                            self.bump_char();
                        }
                        let esc_loc = self.curr_loc();
                        match self.current_char() {
                            c if is_hex(c) => {
                                let (a, b) = self.eat_while(is_hex);
                                if self.on_char('\'') {
                                    self.bump_char();
                                    if a == b {
                                        self.bump_char();
                                        Token::Error(LexError::InvalidUnicode(
                                            esc_loc,
                                            CodePointError::Empty,
                                        ))
                                    } else if b - a <= 6 {
                                        self.bump_char();
                                        let s = &self.src[a..b];
                                        let int = u32::from_str_radix(s, 16).expect(
                                            "all characters are known to be ascii hex digits",
                                        );
                                        if let Some(c) = char::from_u32(int) {
                                            Token::Char(c)
                                        } else {
                                            Token::Error(LexError::InvalidUnicode(
                                                esc_loc,
                                                CodePointError::NotInCharRange(
                                                    Symbol::intern(s),
                                                    int,
                                                ),
                                            ))
                                        }
                                    } else {
                                        Token::Error(LexError::InvalidUnicode(
                                            esc_loc,
                                            CodePointError::TooLong(Symbol::intern(
                                                &self.src[a..b],
                                            )),
                                        ))
                                    }
                                } else {
                                    self.eat_while(|c| c != '\'');
                                    let end = self.curr_loc();
                                    Token::Error(LexError::UnterminatedChar(loc, end))
                                }
                            }
                            c => {
                                self.eat_while(|c| c != '\'');
                                Token::Error(LexError::InvalidUnicode(
                                    esc_loc,
                                    CodePointError::BadConnector(c),
                                ))
                            }
                        }
                    }
                    Some(c) if grapheme::is_escapable(c) => {
                        let esc = grapheme::get_escaped(*c);
                        self.bump_char();
                        if self.on_char('\'') {
                            self.bump_and(Token::Lit(Literal::Char(esc)))
                        } else {
                            self.eat_while(|c| c != '\'');
                            let end = self.prev_loc();
                            self.bump_and(Token::Error(LexError::UnterminatedChar(loc, end)))
                        }
                    }
                    Some(c) => {
                        let c = *c;
                        self.eat_while(|c| c != '\'');
                        let end = self.prev_loc();
                        self.bump_and(Token::Error(LexError::InvalidEscape(c, loc, end)))
                    }
                    None => Token::Error(LexError::UnterminatedChar(loc, self.prev_loc())),
                }
            }
            '\0' => Token::Error(LexError::UnterminatedChar(loc, self.prev_loc())),
            c => {
                let id_candidate = grapheme::is_ident_start(c);
                let start = self.pos;
                self.bump_char();
                if self.on_char('\'') {
                    self.bump_and(Token::Char(c))
                } else {
                    // maybe it's a promoted operator, like `'foo` or
                    // `'a
                    if self.on_char(char::is_whitespace as fn(char) -> bool) {
                        self.bump_char();
                        Token::Affix(Symbol::intern(&self.src[start..self.pos]), true)
                    } else if id_candidate {
                        let (_, end) = self.eat_with_trailing(grapheme::is_ident_char);
                        Token::Affix(Symbol::intern(&self.src[start..end]), true)
                    } else {
                        let end = self.prev_loc();
                        let (_, _end) = self
                            .eat_while(|c| c != '\'' && c.is_alphanumeric() || matches!(c, '_'));
                        Token::Error(LexError::UnterminatedChar(loc, end))
                    }
                }
            }
        }
    }

    fn string(&mut self) -> Token {
        let mut buf = String::new();
        let start = self.prev_loc();
        self.bump_char();
        let mut escaped = false;
        let mut terminated = false;
        while let Char::Chr(c) = self.bump_char() {
            if escaped {
                escaped = false;
                match c {
                    esc if grapheme::is_escapable(&esc) => buf.push(grapheme::get_escaped(esc)),
                    '\n' => {
                        self.eat_whitespace();
                    }
                    c => buf.push(c),
                };
            } else if c == '"' {
                terminated = true;
                break;
            } else if c == '\\' {
                escaped = true;
            } else {
                buf.push(c);
            }
        }
        if terminated {
            Token::Str(Symbol::intern(buf))
        } else {
            Token::Error(LexError::UnterminatedString(start))
        }
    }

    #[inline]
    fn line_comment(&mut self) -> (usize, usize) {
        self.eat_while(|c| c != '\n')
    }

    fn block_comment(&mut self) -> Option<LexError> {
        let mut depth = 1;
        let mut interrupted = false;
        let start = self.prev_loc();
        let mut end = self.prev_loc();
        loop {
            if depth == 0 {
                break;
            }
            if self.is_done() {
                interrupted = true;
                break;
            }
            match self.peek_char() {
                Some('~') => {
                    self.bump_char();
                    if self.on_char('{') {
                        depth += 1;
                    }
                }
                Some('}') => {
                    self.bump_char();
                    if self.on_char('~') {
                        depth -= 1;
                        self.bump_char();
                    }
                }
                _ => {
                    end = self.prev_loc();
                    self.bump_char();
                    continue;
                }
            }
        }
        if interrupted {
            Some(LexError::UnterminatedComment(start, end))
        } else {
            // since we stopped at the last `~`, we consume it
            self.bump_char();
            // TODO: keep or ignore block comments?
            None
        }
    }
}

#[inline]
fn identifier(c: char) -> impl FnOnce(&str) -> Token {
    assert!(
        c.is_lowercase(),
        "the first character of an identifier must \
                be an underscore '_' or an alphabetic character, \
                but {c:?} is neither"
    );
    move |s: &str| {
        (if c.is_uppercase() {
            Token::Upper
        } else {
            Token::Lower
        })(Symbol::intern(s))
    }
}

impl<'t> Iterator for Lexer<'t> {
    type Item = (Token, LocSpan);

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.lex();
        let lo = self.prev_loc();
        let hi = self.curr_loc();
        if token.is_eof() {
            None
        } else {
            Some((token, LocSpan::new(lo, hi)))
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn token_positions() {
        let src = r#"
'\u005c' 'elem
"#;
        let mut lexer = Lexer::new(src);
        for ((actual, actual_locspan), (expected, expected_locspan)) in lexer.by_ref().zip([
            (
                Token::Lit(Literal::Char('\\')),
                LocSpan {
                    lo: Loc {
                        line: 2,
                        col: 1,
                        pos: 1,
                    },
                    hi: Loc {
                        line: 2,
                        col: 10,
                        pos: 10,
                    },
                },
            ),
            (
                Token::Affix(Symbol::intern("elem"), true),
                LocSpan {
                    lo: Loc {
                        line: 2,
                        col: 10,
                        pos: 10,
                    },
                    hi: Loc {
                        line: 2,
                        col: 15,
                        pos: 15,
                    },
                },
            ),
        ]) {
            assert_eq!(actual, expected);
            assert_eq!(actual_locspan, expected_locspan);
        }
    }
}
