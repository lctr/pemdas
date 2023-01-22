use crate::{
    syntax::ast::Infix,
    text::{grapheme::Match, symbol::Symbol},
};

use super::{
    ast::{Ast, Decl, Expr, ExprDecl, Ident, InfixDecl, Pat},
    fixity::{Assoc, Fixity, Prec},
    lexer::Lexer,
    token::{Literal, Loc, Token},
};

#[derive(Clone, PartialEq, Debug)]
pub enum Error {
    Expected(Token, Loc, Token),
    Unexpected(Token, Loc),
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Error::Expected(_, loc, _) | Error::Unexpected(_, loc) => *loc,
        }
    }

    pub fn write_without_loc(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Expected(tok, _, found) => {
                write!(f, "expected `{}`, but found `{}`", tok, found)
            }
            Error::Unexpected(tok, _) => {
                write!(f, "unexpected token `{}`", tok)
            }
        }
    }

    pub fn write_with_path(
        &self,
        p: impl AsRef<std::path::Path>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.write_without_loc(f)?;
        let loc = self.loc();
        write!(
            f,
            "\n @ {}:{}:{}",
            p.as_ref().display(),
            &loc.line,
            &loc.col
        )
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Expected(tok, loc, found) => {
                write!(f, "expected `{}`, but found `{}` at {}", tok, found, loc)
            }
            Error::Unexpected(tok, loc) => {
                write!(f, "unexpected token `{}` found at {}", tok, loc)
            }
        }
    }
}

pub type Parsed<T> = Result<T, Error>;

pub struct Parser<'t> {
    lexer: Lexer<'t>,
}

impl<'t> Parser<'t> {
    pub fn new(src: &'t str) -> Self {
        Self {
            lexer: Lexer::new(src),
        }
    }

    pub fn is_done(&mut self) -> bool {
        match self.lexer.peek() {
            None | Some(Token::Eof) => true,
            _ => false,
        }
    }

    fn peek(&mut self) -> &Token {
        self.lexer.peek().unwrap_or_else(|| &Token::Eof)
    }

    fn peek_on(&mut self, lexeme: impl Match<Token>) -> bool {
        lexeme.check(self.peek())
    }

    fn bump(&mut self) -> Token {
        self.lexer.bump()
    }

    fn bump_on(&mut self, lexeme: impl Match<Token>) -> bool {
        let on = self.peek_on(lexeme);
        if on {
            self.bump();
        }
        on
    }

    pub fn ignore(&mut self, lexeme: impl Match<Token>) {
        self.bump_on(lexeme);
    }

    fn eat(&mut self, token: Token) -> Parsed<(Loc, Loc)> {
        let loc = self.lexer.curr_loc();
        let t = *(self.peek());
        if t == token {
            self.bump();
            Ok((loc, self.lexer.curr_loc()))
        } else {
            Err(Error::Expected(token, loc, t))
        }
    }

    pub fn eat_then<X>(
        &mut self,
        token: Token,
        f: impl FnOnce(&mut Self) -> Parsed<X>,
    ) -> Parsed<X> {
        self.eat(token)?;
        f(self)
    }

    pub fn bump_then<X>(&mut self, f: impl FnOnce(&mut Self) -> X) -> X {
        self.bump();
        f(self)
    }

    pub fn sep_by1<X>(
        &mut self,
        sep: Token,
        mut f: impl FnMut(&mut Self) -> Parsed<X>,
    ) -> Parsed<Vec<X>> {
        let mut node = vec![f(self)?];
        while self.bump_on(&sep) {
            node.push(f(self)?);
        }
        Ok(node)
    }

    pub fn parse(&mut self) -> Parsed<Ast> {
        let mut ast = Ast::default();
        self.parse_into(&mut ast)?;
        Ok(ast)
    }

    pub fn parse_into(&mut self, ast: &mut Ast) -> Parsed<()> {
        while !self.is_done() {
            match self.peek() {
                Token::Eof => break,
                _ => ast.push(self.decl()?),
            };
            self.ignore(Token::Semi);
        }
        Ok(())
    }

    fn decl(&mut self) -> Parsed<Decl> {
        let loc = self.lexer.curr_loc();
        match self.peek() {
            Token::InfixL | Token::InfixR | Token::Infix => Ok(Decl::Infix(self.infix_decl()?)),
            t if begins_expr(t, true) => Ok(Decl::Expr(ExprDecl {
                expr: self.expression()?,
            })),
            &t => Err(Error::Unexpected(t, loc)),
        }
    }

    pub fn infix_decl(&mut self) -> Parsed<InfixDecl> {
        let fixity = self.fixity()?;
        let mut infixes = vec![self.infix()?];
        while self.bump_on(Token::Comma) {
            infixes.push(self.infix()?);
        }
        Ok(InfixDecl { infixes, fixity })
    }

    pub fn fixity(&mut self) -> Parsed<Fixity> {
        let assoc = {
            let loc = self.lexer.curr_loc();
            match self.peek() {
                Token::InfixL => self.bump_then(|_| Ok(Assoc::Left)),
                Token::InfixR => self.bump_then(|_| Ok(Assoc::Right)),
                Token::Infix => self.bump_then(|_| Ok(Assoc::Neither)),
                &t => Err(Error::Unexpected(t, loc)),
            }
        }?;
        let prec = {
            let loc = self.lexer.curr_loc();
            match self.peek() {
                &Token::Lit(Literal::Int(n)) => {
                    self.bump();
                    if n <= (Prec::MAX_VAL as usize) {
                        Ok(Prec(n as u8))
                    } else {
                        todo!("Precedence values must be between 0 and 9 inclusive, but `{n}` was provided")
                    }
                }
                Token::Affix(..) => Ok(Prec::default()),
                &t => Err(Error::Unexpected(t, loc)),
            }
        }?;
        Ok(Fixity { prec, assoc })
    }

    pub fn expression(&mut self) -> Parsed<Expr> {
        self.binary(Self::subexpression)
    }

    pub fn subexpression(&mut self) -> Parsed<Expr> {
        self.application(Self::atom)
    }

    pub fn application(&mut self, mut f: impl FnMut(&mut Self) -> Parsed<Expr>) -> Parsed<Expr> {
        let loc = self.lexer.curr_loc();
        let column = |this: &mut Self| this.lexer.curr_loc().col > loc.col;
        let mut expr = f(self)?;
        while arg_expr_tok(self.peek()) && column(self) {
            expr = Expr::App(Box::new(expr), Box::new(f(self)?));
        }
        Ok(expr)
    }

    pub fn binary(&mut self, mut f: impl FnMut(&mut Self) -> Parsed<Expr>) -> Parsed<Expr> {
        fn reduce(stack: Vec<(Expr, Infix)>, last: Expr) -> Expr {
            stack.into_iter().rfold(last, |right, (left, infix)| {
                Expr::Bin(Box::new(left), infix, Box::new(right))
            })
        }
        let mut left = f(self)?;
        let mut stack = vec![];
        let mut lncol;
        while let Ok(affix) = self.infix() {
            lncol = self.lexer.curr_loc();
            match self.peek() {
                t if begins_expr(t, false) => {
                    stack.push((left, affix));
                    left = f(self)?;
                }
                &found => return Err(Error::Unexpected(found, lncol)),
            }
        }

        Ok(reduce(stack, left))
    }

    pub fn infix(&mut self) -> Parsed<Infix> {
        let loc = self.lexer.curr_loc();
        match *(self.peek()) {
            Token::Dash => self.bump_then(|_| Ok(Infix::Standard(Symbol::DASH))),
            Token::At => self.bump_then(|_| Ok(Infix::Standard(Symbol::AT))),
            Token::Affix(s, promoted) => self.bump_then(|_| {
                Ok((if promoted {
                    Infix::Promoted
                } else {
                    Infix::Standard
                })(s))
            }),
            t => Err(Error::Unexpected(t, loc)),
        }
    }

    pub fn pattern(&mut self) -> Parsed<Pat> {
        let loc = self.lexer.curr_loc();
        match self.peek() {
            Token::Underscore => self.bump_then(|_| Ok(Pat::Wild)),
            Token::ParenL => self.paren_pat(),
            Token::BrackL => self.brack_pat(),
            &Token::Upper(s) => self.bump_then(|_| Ok(Pat::Con(s, vec![]))),
            &Token::Lower(s) => self.lower_pat(s),
            &t => Err(Error::Unexpected(t, loc)),
        }
    }

    pub fn inner_pat(&mut self) -> Parsed<Pat> {
        let loc = self.lexer.curr_loc();
        match self.peek() {
            Token::Underscore => self.bump_then(|_| Ok(Pat::Wild)),
            Token::ParenL => self.paren_pat(),
            Token::BrackL => self.brack_pat(),
            &Token::Upper(con) => self.upper_pat(con),
            &Token::Lower(s) => self.lower_pat(s),
            &Token::Lit(lit) => self.bump_then(|_| Ok(Pat::Lit(lit))),
            Token::Dash => self.bump_then(Self::pattern),
            &t => Err(Error::Unexpected(t, loc)),
        }
    }

    pub fn brack_pat(&mut self) -> Parsed<Pat> {
        self.eat(Token::BrackL)?;
        let pat = if self.bump_on(Token::BrackR) {
            Ok(Pat::Arr(vec![]))
        } else {
            let first = self.inner_pat()?;
            self.collection_tail(first, Self::inner_pat, Pat::Arr)
        }?;
        self.eat_then(Token::BrackR, move |_| Ok(pat))
    }

    pub fn upper_pat(&mut self, ctor: Symbol) -> Parsed<Pat> {
        self.bump();
        let mut args = vec![];
        while begins_pat(self.peek(), false) {
            args.push(self.pattern()?);
        }

        let pat = Pat::Con(ctor, args);
        if self.peek_on(Token::Comma) {
            self.collection_tail(pat, Self::pattern, Pat::Tup)
        } else {
            Ok(pat)
        }
    }

    pub fn lower_pat(&mut self, var: Symbol) -> Parsed<Pat> {
        self.bump();
        if self.bump_on(Token::At) {
            Ok(Pat::As(var, Box::new(self.pattern()?)))
        } else {
            Ok(Pat::Var(var))
        }
    }

    pub fn paren_pat(&mut self) -> Parsed<Pat> {
        self.eat(Token::ParenL)?;
        let loc = self.lexer.curr_loc();
        let mut pat = match self.peek() {
            &Token::Affix(s, _) => {
                self.bump();
                Ok(Pat::Var(s))
            }
            &Token::Upper(con) => {
                let pat = self.upper_pat(con)?;
                Ok(pat)
            }
            &Token::Dash => {
                self.bump();
                let pat = self.pattern()?;
                Ok(Pat::Neg(Box::new(pat)))
            }
            t if begins_pat(t, true) => self.pattern(),
            &t => Err(Error::Unexpected(t, loc)),
        }?;
        if self.peek_on(Token::Comma) {
            pat = self.collection_tail(pat, Self::inner_pat, Pat::Tup)?;
        }
        self.eat_then(Token::ParenR, |_| Ok(pat))
    }

    pub fn collection_tail<X>(
        &mut self,
        first: X,
        mut each: impl FnMut(&mut Self) -> Parsed<X>,
        wrap: fn(Vec<X>) -> X,
    ) -> Parsed<X> {
        let mut elems = vec![first];
        while self.bump_on(Token::Comma) {
            elems.push(each(self)?);
        }
        Ok(wrap(elems))
    }

    pub fn lambda(&mut self) -> Parsed<Expr> {
        self.eat(Token::Lambda)?;
        let mut pats = vec![self.pattern()?];
        while begins_pat(self.peek(), false) {
            pats.push(self.pattern()?);
        }
        self.eat(Token::Arrow)?;
        let body = self.expression()?;
        Ok(pats
            .into_iter()
            .rfold(body, |expr, pat| Expr::Lam(pat, Box::new(expr))))
    }

    fn paren_expr(&mut self) -> Parsed<Expr> {
        self.eat(Token::ParenL)?;
        let loc = self.lexer.curr_loc();
        match self.peek() {
            Token::ParenR => {
                self.bump();
                Ok(Expr::UNIT)
            }
            &Token::Affix(s, _) => {
                self.bump();
                self.eat(Token::ParenR)?;
                Ok(Expr::Var(Ident::Infix(s)))
            }
            Token::Comma => {
                let mut count = 0;
                while self.bump_on(Token::Comma) {
                    count += 1;
                }
                self.eat(Token::ParenR)?;
                Ok(Expr::Var(Ident::Commas(count)))
            }
            t if begins_expr(t, true) => {
                let first = self.expression()?;
                if self.peek_on(Token::Comma) {
                    let mut elems = vec![first];
                    while self.bump_on(Token::Comma) {
                        elems.push(self.expression()?);
                    }
                    self.eat(Token::ParenR)?;
                    Ok(Expr::Tup(elems))
                } else {
                    self.eat(Token::ParenR)?;
                    Ok(Expr::Grp(Box::new(first)))
                }
            }
            &t => Err(Error::Unexpected(t, loc)),
        }
    }

    fn brack_expr(&mut self) -> Parsed<Expr> {
        self.eat(Token::BrackL)?;
        let mut elems = vec![];
        while !self.is_done() && !self.peek_on(Token::BrackR) {
            elems.push(self.expression()?);
            if self.peek_on(Token::Comma) {
                self.bump();
            }
        }
        self.eat(Token::BrackR)?;
        Ok(Expr::List(elems))
    }

    pub fn atom(&mut self) -> Parsed<Expr> {
        let loc = self.lexer.curr_loc();
        match self.peek() {
            Token::Lambda => self.lambda(),
            Token::ParenL => self.paren_expr(),
            Token::BrackL => self.brack_expr(),
            Token::Let => {
                self.bump();
                let fixity = self.infix_decl()?;
                self.eat(Token::In)?;
                let body = self.expression()?;
                Ok(Expr::Let(fixity, Box::new(body)))
            }
            &Token::Lit(lit) => {
                self.bump();
                Ok(Expr::Lit(lit))
            }
            &Token::Upper(s) => {
                self.bump();
                Ok(Expr::Var(Ident::Upper(s)))
            }
            &Token::Lower(s) => {
                self.bump();
                Ok(Expr::Var(Ident::Lower(s)))
            }
            &t => Err(Error::Unexpected(t, loc)),
        }
    }
}

pub fn begins_expr(tok: &Token, allow_neg: bool) -> bool {
    match tok {
        Token::ParenL
        | Token::BrackL
        | Token::Lambda
        | Token::Let
        | Token::Lit(_)
        | Token::Upper(_)
        | Token::Lower(_) => true,
        Token::Dash => allow_neg,
        _ => false,
    }
}

pub fn arg_expr_tok(tok: &Token) -> bool {
    matches! {tok,
        Token::ParenL | Token::BrackL | Token::Lit(_) | Token::Upper(_) | Token::Lower(_)
    }
}

pub fn begins_pat(tok: &Token, allow_neg: bool) -> bool {
    match tok {
        Token::Underscore
        | Token::ParenL
        | Token::ParenR
        | Token::BrackL
        | Token::BrackR
        | Token::Upper(_)
        | Token::Lower(_) => true,
        Token::Dash => allow_neg,
        _ => false,
    }
}

pub fn parse_expr(src: &str) -> Parsed<Expr> {
    Parser::new(src).expression()
}

pub fn parse(src: &str) -> Parsed<Ast> {
    Parser::new(src).parse()
}

#[cfg(test)]
mod test {
    use crate::syntax::ast::DeclKind;

    use super::*;

    trait Echo {
        fn echo(self) -> Self
        where
            Self: Sized,
        {
            self.debug();
            self
        }

        fn echo_ref(&self) -> &Self {
            self.debug();
            self
        }

        fn echo_mut(&mut self) -> &mut Self {
            self.debug();
            self
        }

        fn echo_then<X>(self, f: impl FnOnce(Self) -> X) -> X
        where
            Self: Sized,
        {
            f(self.echo())
        }

        fn echo_err(self) -> Self
        where
            Self: Sized;

        fn debug(&self);
    }

    impl<X, E> Echo for Result<X, E>
    where
        X: std::fmt::Debug,
        E: std::fmt::Display,
    {
        fn debug(&self) {
            match self {
                Ok(x) => println!("{x:#?}"),
                Err(e) => println!("{e}"),
            }
        }

        fn echo_err(self) -> Self {
            self.map_err(|e| {
                println!("{e}");
                e
            })
        }
    }

    macro_rules! tree {
        (()) => {
            From::from(())
        };
        ([]) => {
            From::from([])
        };
        (Int $lit:literal) => {{
            crate::syntax::ast::Expr::Lit(
                crate::syntax::token::Literal::Int(
                    $lit
                )
            )
        }};
        (Sym $name:ident) =>  {
            crate::text::symbol::Symbol::intern(stringify!($name))
        };
        (Lower $name:ident) => {
            crate::syntax::ast::Ident::Lower(tree!(Sym $name))
        };
        (Upper $name:ident) => {
            crate::syntax::ast::Ident::Upper(tree!(Sym $name))
        };
        (Infix $($t:tt)+) => {{
            crate::syntax::ast::Ident::Infix(
                crate::text::Symbol::intern(
                    concat!($(stringify!($t)),+)
                )
            )
        }};
        (E.Lower $t:ident) => {
            crate::syntax::ast::Expr::Var(tree! { Lower $t })
        };
        (E.Infix $($t:tt)+) => {{
            crate::syntax::ast::Expr::Var(tree! { Infix $($t)+ })
        }};
        (E.Tup $(($($ts:tt)+))*) => {{
            crate::syntax::ast::Expr::Tup(
                vec![$(tree! { ~ $($ts)+ }),*]
            )
        }};
        (E.List $(($($ts:tt)+))*) => {{
            crate::syntax::ast::Expr::List(
                vec![$(tree! { ~ $($ts)+ }),*]
            )
        }};
        (P.Var $t:ident) => {
            crate::syntax::ast::Pat::Var(
                tree!(Sym $t)
            )
        };
        (P.Con $con:ident $($t:tt)*) => {{
            use crate::syntax::ast::Pat;
            Pat::Con(
                tree!(Sym $con),
                vec![$(tree! { ~ $t },)*]
            )
        }};
        (P.As $var:ident $($t:tt)+) => {{
            crate::syntax::ast::Pat::As(
                tree!(Sym $var),
                Box::new(tree! { ~ $($t)+ })
            )
        }};
        (P.Tup $(($($ts:tt)+))*) => {{
            crate::syntax::ast::Pat::Tup(
                vec![$(tree! { ~ $($ts)+ }),*]
            )
        }};
        (P.Arr $(($($ts:tt)+))*) => {{
            crate::syntax::ast::Pat::Arr(
                vec![$(tree! { ~ $($ts)+ }),*]
            )
        }};
        (~ $($t:tt)+) => {{
            tree! { $($t)+ }
        }};
        (# $($t:tt)+) => {{
            macro_rules! __force_expr {
                ($e:expr) => {{ $e }};
            }
            __force_expr!( $($t)+ )
        }};
        (App ($($ls:tt)+) ($($rs:tt)+) $($(($($ts:tt)+))+)?) => {{
            use crate::syntax::ast::Expr;
            let _app = Expr::App(
                Box::new(tree! { ~ $($ls)+ }),
                Box::new(tree! { ~ $($rs)+ })
            );
            $($(let _app = Expr::App(
                Box::new(_app),
                Box::new(tree! { ~ $($ts)+ })
            );)+)?
            _app
        }};
        (Lam $(($($ps:tt)+))+ -> { $($es:tt)+ }) => {{
            vec![$(tree! { ~ $($ps)+ }),+]
                .into_iter()
                .rfold(
                    tree! { ~ $($es)+ },
                    |expr, pat| crate::syntax::ast::Expr::Lam(
                        pat,
                        Box::new(expr)
                    )
                )
        }};
    }

    fn assert_src_expr(src: &str, expr: Expr) {
        assert_eq!(
            Parser::new(src).expression().echo_err(),
            Ok(expr),
            "testing that\n    `{src}`\nparses correctly"
        );
    }

    #[test]
    fn test_fixity() {
        assert_eq!(
            Parser::new("infixr 5 :, +").parse().unwrap(),
            Ast {
                kinds: vec!(DeclKind::Infix),
                infxs: vec!(InfixDecl {
                    infixes: vec![
                        Infix::Standard(Symbol::COLON),
                        Infix::Standard(Symbol::PLUS)
                    ],
                    fixity: Fixity {
                        assoc: Assoc::Right,
                        prec: Prec(5)
                    }
                }),
                exprs: vec!()
            }
        );
    }

    #[test]
    fn test_lambda() {
        for (src, expr) in [
            (
                r#"\x y z -> x y z"#,
                tree! {
                    Lam (P.Var x) (P.Var y) (P.Var z) -> {
                        App (E.Lower x) (E.Lower y) (E.Lower z)
                    }
                },
            ),
            (
                r#"\x (x, y) -> (x, y)"#,
                tree! {
                    Lam (P.Var x) (P.Tup (P.Var x) (P.Var y)) -> {
                        E.Tup (E.Lower x) (E.Lower y)
                    }
                },
            ),
        ] {
            assert_src_expr(src, expr)
        }
    }

    #[test]
    fn test_tuple() {
        for (src, expr) in [
            ("()", tree! { () }),
            ("(a, b)", tree! { E.Tup (E.Lower a) (E.Lower b) }),
        ] {
            assert_src_expr(src, expr)
        }
    }

    #[test]
    fn test_app() {
        for (src, expr) in [
            (r#"f x"#, tree! { App (E.Lower f) (E.Lower x) }),
            (
                r#"f x (y, z)"#,
                tree! { App (E.Lower f) (E.Lower x) (E.Tup (E.Lower y) (E.Lower z)) },
            ),
            ("f x\ny", tree! { App (E.Lower f) (E.Lower x) }),
        ] {
            assert_src_expr(src, expr)
        }
    }
}
