use std::fmt;

use super::lexicon::INTERNER;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(pub(crate) u32);

impl Symbol {
    pub const fn as_u64(&self) -> u64 {
        self.0 as u64
    }

    pub const fn as_u32(&self) -> u32 {
        self.0
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        INTERNER.lookup(*self)
    }

    #[inline]
    pub fn by_str<T>(&self, mut f: impl FnMut(&str) -> T) -> T {
        f(self.as_str())
    }

    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    #[inline]
    pub fn intern(s: impl AsRef<str>) -> Self {
        INTERNER.intern(s)
    }

    pub fn intern_iter<J, I>(iter: I) -> J
    where
        I: IntoIterator,
        I::Item: AsRef<str>,
        J: FromIterator<Symbol>,
    {
        INTERNER.intern_iter(iter)
    }

    pub fn debug(self) -> DebugSymbol {
        DebugSymbol(self)
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<Symbol> for str {
    fn eq(&self, other: &Symbol) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<char> for Symbol {
    fn eq(&self, other: &char) -> bool {
        let s = self.as_str();
        other.len_utf8() == s.len() && {
            let mut cs = s.chars();
            matches!(cs.next(), Some(c) if c == *other) && cs.next().is_none()
        }
    }
}

impl std::ops::Deref for Symbol {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl std::borrow::Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

pub struct DebugSymbol(Symbol);

impl fmt::Debug for DebugSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Symbol").field(&self.0).finish()
    }
}

impl fmt::Display for DebugSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.as_str().fmt(f)
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({})({:?})", self.0, self.as_str())
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Self::intern(value)
    }
}

pub fn intern_n<S, const N: usize>(ss: [S; N]) -> [Symbol; N]
where
    S: AsRef<str>,
{
    INTERNER.intern_n(ss)
}

#[cfg(test)]
mod test {
    use super::super::lexicon;
    use super::*;

    #[test]
    fn test_predefined_symbols() {
        lexicon::PREDEFINED
            .into_iter()
            .enumerate()
            .for_each(|(n, s)| {
                assert!(n < (u32::MAX as usize));
                let index = n as u32;
                let symbol = Symbol(index);
                assert_eq!(symbol.as_str(), s);
                let interned = INTERNER.intern(s);
                assert_eq!(interned, symbol);
                assert_eq!(interned.as_u32(), index);
            });
    }

    #[test]
    fn test_predefined_predicates() {
        type Pred = fn(&Symbol) -> bool;
        for (txt, pred, sym) in [
            ("", Symbol::is_empty as Pred, Symbol::EMPTY),
            ("_", Symbol::is_underscore, Symbol::UNDERSCORE),
            ("->", Symbol::is_arrow, Symbol::ARROW),
            ("+", Symbol::is_plus, Symbol::PLUS),
        ] {
            let s = lexicon::intern(txt);
            assert_eq!(s, sym);
            assert!(pred(&s));
            assert!(pred(&sym));
        }
    }
}
