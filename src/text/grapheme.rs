/// Returns `true` is `pre` is a prefix of `s` such that the iterator
/// obtained from splitting `s` by whitespace yields `pre` as the
/// first element.
///
/// Note that if `pre` is the empty string, or consists of any
/// whitespace characters, then this function will return `false`.
///
/// For example, the call
/// ```ignore
/// prefix("foo", "foo bar")
/// ```
/// returns `true`, while the call
/// ```ignore
/// prefix("foo", "bar")
/// ```
/// returns `false`.
///
/// Note additionally that the call
/// ```ignore
/// prefix("foo", "fool")
/// ```
/// returns `false`, since the expression
/// ```ignore
/// "fool".split_whitespace().next() == Some("foo")
/// ```
/// returns `false`.
#[inline]
pub fn is_prefix(pre: impl Match<str>, s: &str) -> bool {
    matches!(s.split_whitespace().next(), Some(t) if pre.check(t))
}

/// Returns `true` if the character `c` is valid in a number with a
/// given `radix` based on whether it is the `first` character in the
/// number.
///
/// Since `_` is accepted as a digit *separator* (repeated
/// arbitrarily many times) but *not* as the first character in a
/// number, this function will also return `true` if the character `c`
/// is an underscore `_` but *not* the first character (i.e., when
/// `first` is `false`).
///
/// Note that numeric prefixes are to be handled (and stripped) prior
/// to relying on this function, thus leading to the first character
/// after the prefix to be treated as the first character in the
/// sequence. For example, `"0xF1"` will be stripped to `"F1"` to get a
/// radix of `"16"` should pass as a valid number using this function
/// on character in the stripped form; below is an example where such
/// a string is validated in a lexical fashion using `is_num_char`.
///
/// ```
/// use crate::text::grapheme::is_num_char;
/// let num_str = "0xF1";
/// let mut idx = 0;
/// let radix = {
///     let mut default = 10;
///     if num_str.starts_with('0') {
///         match num_str.chars().skip(1).next() {
///             Some('b'|'B') => default = 2,
///             Some('o'|'O') => default = 8,
///             Some('x'|'X') => default = 16,
///             _ => ()
///         };
///     }
///     // the value was only modified in the presence of prefixes
///     if default != 10 {
///         // since we "0b", "0B", "0o", "0O", 0x" and "0X" are
///         // all of length `2` since each of its characters
///         // has length `1`
///         idx += 2
///     }
///     default
/// };
///
/// assert_eq!(radix, 16);
/// let stripped = &num_str[idx..];
/// assert_eq!(stripped, "F1");
///
/// // how this would be used iteratively/in practice
/// let all_num_chars_by_iter = stripped
///     .chars()
///     .zip([true, false])
///     .all(|(c, is_first)| is_num_char(radix, c, is_first));
///
/// // manually computing the same thing as above
/// let both_num_chars_manually = is_num_char(16, 'F', true)
///     && is_num_char(16, '1', false);
/// // shorthand for testing that they're equal, since `&&` only
/// // returns `true` if both operands are `true`
/// assert!(all_num_chars_by_iter && both_num_chars_manually);
/// ```
///
/// returning `true`. Further examples can be seen in the table below.
///
/// | Char  | Is first | radix | is_num_char | Examples
/// |-------|----------|-------|-------------|----------------
/// | `'1'` | `true`   | `10`  | `true`      | `10`, `1_3`
/// | `'1'` | `false`  | `2`   | `true`      | `0b01`
/// | `'f'` | `true`   | `16`  | `true`      | `0xff`
/// | `'f'` | `true`   | `10`  | `false`     | `0bff`
/// | `'_'` | `true`   | `10`  | `false`     | `_0_00_1`
/// | `'_'` | `false`  | `10`  | `true`      | `1_000_000`
/// | `'8'` | `true`   | `8`   | `false`     | `0o88`
/// | `'8'` | `false`  | `8`   | `false`     | `0o48`
///
pub fn is_num_char(radix: u32, c: char, first: bool) -> bool {
    c.is_digit(radix) || (!first && c == '_')
}

/// Returns `true` if the given character is an underscore `_` or
/// whether it has case.
pub fn is_ident_start(c: char) -> bool {
    c == '_' || has_case(c)
}

/// Returns `true` if the given character is an underscore `_` or
/// has the `Alphabetic` property of the [Unicode standard] as
/// specified in [Unicode Character Database][ucd]
/// [`DerivedCoreProperties.txt`].
///
/// [Unicode standard]: https://www.unicode.org/versions/latest/
/// [ucd]: https://www.unicode.org/reports/tr44/
/// [`DerivedCoreProperties`]:
///     https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt
pub fn is_ident_start_ext(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

/// Identifies whether a character has case.
///
/// ```
/// use crate::text::grapheme::has_case;
///
/// assert!(has_case('a'));
/// assert!(has_case('α'));
/// assert!(has_case('Θ'));
/// assert!(!has_case('+'));
/// assert!(!has_case(' '));
///
/// // The various Chinese scripts and punctuation do not have case, and so:
/// assert!(!has_case('中'));
/// ```
pub fn has_case(c: char) -> bool {
    c.is_uppercase() || c.is_lowercase()
}

/// Identifies whether a character is a valid non-initial character in
/// a non-infix/non-operator identifier.
///
/// Returns `true` if the given character is either an underscore `_`,
/// an apostrophe `'`, or it satisfies `char::is_alphanumeric`.
#[inline]
pub fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '\'')
}

/// Returns `true` if the given character is a backslash `\` or any
/// one of `~!@#$%^&*-+=<>/:|?.`.
pub const fn is_infix_char(c: char) -> bool {
    matches!(
        c,
        '~' | '!'
            | '@'
            | '#'
            | '$'
            | '%'
            | '^'
            | '&'
            | '*'
            | '-'
            | '+'
            | '='
            | '<'
            | '>'
            | '/'
            | '\\'
            | ':'
            | '|'
            | '?'
            | '.'
    )
}

#[inline]
pub const fn is_subscript(c: char) -> bool {
    matches!(
        c,
        '₀' | '₁'
            | '₂'
            | '₃'
            | '₄'
            | '₅'
            | '₆'
            | '₇'
            | '₈'
            | '₉'
            | '₍'
            | '₎'
            | '₊'
            | '₋'
    )
}

#[inline]
pub const fn is_superscript(c: char) -> bool {
    matches!(
        c,
        '⁰' | '¹'
            | '²'
            | '³'
            | '⁴'
            | '⁵'
            | '⁶'
            | '⁷'
            | '⁸'
            | '⁹'
            | '⁽'
            | '⁾'
            | '⁺'
            | '⁻'
    )
}

/// Returns `true` if the given character is a superscript or
/// subscript character.
#[inline]
pub const fn is_trailing(c: char) -> bool {
    is_subscript(c) || is_superscript(c)
}

pub const fn get_escaped(c: char) -> char {
    match c {
        't' => '\t',
        'n' => '\n',
        'r' => '\r',
        '"' => '\"',
        '\'' => '\'',
        '\\' => '\\',
        'b' => '\x08',
        'f' => '\x0C',
        c => c,
    }
}

pub const fn is_escapable(c: &char) -> bool {
    matches!(*c, 't' | 'n' | 'r' | '"' | '\'' | '\\' | 'b' | 'f')
}

/// Returns a string slice from a given a slice of (UTF8-encoded)
/// bytes. If not valid UTF-8, then `None` is returned.
pub const fn bytestring<'a>(bytes: &'a [u8]) -> Option<&'a str> {
    if let Ok(s) = std::str::from_utf8(bytes) {
        Some(s)
    } else {
        None
    }
    // std::mem::transmute::<&'a [u8], &'a str>(bytes)
}

pub fn charstring<'a, I>(chars: I) -> &'a str
where
    I: 'a + Iterator<Item = char>,
    char: 'a,
{
    let (len, chars) = chars.into_iter().fold((0, vec![]), |(mut len, mut cs), c| {
        len += c.len_utf8();
        cs.push(c);
        (len, cs)
    });
    let mut buf = vec![0; len];
    let mut i = 0;
    for c in chars {
        let len = c.len_utf8();
        c.encode_utf8(&mut buf[i..i + len]);
        i += len;
    }
    // Safety: the slice of bytes used is correctly UTF8-encoded.
    unsafe { std::mem::transmute::<_, &'a str>(&buf[..]) }
}

pub fn combine_chars<'a, I>(pre: &'a [char], chars: I, post: &'a [char]) -> &'a str
where
    I: 'a + Iterator<Item = char>,
    I::Item: 'a,
    char: 'a,
{
    let l0 = chars.size_hint().0;
    let (len, cs) = pre
        .into_iter()
        .copied()
        .chain(chars.into_iter())
        .chain(post.into_iter().copied())
        .fold(
            (0, Vec::with_capacity(pre.len() + l0 + post.len())),
            |(mut len, mut cs), c| {
                len += c.len_utf8();
                cs.push(c);
                (len, cs)
            },
        );
    let mut buf = vec![0; len];
    let mut i = 0;
    for c in cs {
        let len = c.len_utf8();
        c.encode_utf8(&mut buf[i..i + len]);
        i += len;
    }
    // Safety: the slice of bytes used is correctly UTF8-encoded by construction
    unsafe { std::mem::transmute::<_, &'a str>(&buf[..]) }
}

/// A simple trait allowing for the use of various types to compare
/// values for equality.
pub trait Match<T: ?Sized> {
    fn check(&self, with: &T) -> bool;
}

impl Match<char> for Option<&char> {
    fn check(&self, with: &char) -> bool {
        matches!(self, Some(c) if *c == with)
    }
}

impl Match<str> for char {
    fn check(&self, with: &str) -> bool {
        self.len_utf8() == with.len() && {
            let mut cs = with.chars();
            cs.next() == Some(*self) && cs.next().is_none()
        }
    }
}

impl Match<char> for str {
    fn check(&self, with: &char) -> bool {
        with.check(self)
    }
}

impl<T> Match<T> for T
where
    T: PartialEq,
{
    fn check(&self, with: &T) -> bool {
        self == with
    }
}

impl<T> Match<T> for &T
where
    T: ?Sized + PartialEq,
{
    fn check(&self, with: &T) -> bool {
        *self == with
    }
}

impl<T> Match<T> for fn(&T) -> bool
where
    T: ?Sized,
{
    fn check(&self, with: &T) -> bool {
        self(with)
    }
}

impl<T> Match<T> for fn(T) -> bool
where
    T: Copy,
{
    fn check(&self, with: &T) -> bool {
        (self)(*with)
    }
}

impl<T, S> Match<S> for [T]
where
    T: Match<S>,
{
    fn check(&self, with: &S) -> bool {
        for t in self {
            if t.check(with) {
                return true;
            }
        }
        false
    }
}

/// Returns the number of digits in an integer in a given base.
pub const fn numlen_base<const BASE: usize>(mut n: usize) -> usize {
    if n == 0 {
        1
    } else {
        let mut k = 0;
        while n > 0 {
            k += 1;
            n /= BASE;
        }
        k
    }
}

/// Returns the number of digits in a base 10 integer. Corresponds to
/// the length of the string representing the number, with leading 0's removed.
pub const fn numlen(n: usize) -> usize {
    numlen_base::<10>(n)
}

#[test]
fn test_digits() {
    for i in 0..9 {
        assert!(numlen(i) == 1);
    }
    for i in 10..99 {
        assert!(numlen(i) == 2);
    }
    for i in 100..999 {
        assert!(numlen(i) == 3);
    }
    for i in 1000..9999 {
        assert!(numlen(i) == 4);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum IntPrefix {
    Bin = 2,
    Oct = 8,
    Hex = 16,
}

impl IntPrefix {
    pub const fn from_char(ch: char) -> Option<Self> {
        match ch {
            'b' | 'B' => Some(Self::Bin),
            'o' | 'O' => Some(Self::Oct),
            'x' | 'X' => Some(Self::Hex),
            _ => None,
        }
    }

    pub const fn radix(&self) -> u32 {
        *self as u32
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bytes_as_str() {
        let bs = b"foo bar baz";
        let input = "foo bar baz";
        let mut buf = vec![0; input.len()];
        let mut i = 0;
        for c in input.chars() {
            let w = c.len_utf8();
            c.encode_utf8(&mut buf[i..i + w]);
            i += w;
        }
        assert_eq!(&buf[..], &bs[..]);
        assert_eq!(bytestring(&buf), Some(input));
        assert_eq!(charstring(input.chars()), input);
        println!("\\u{:x}", '\\' as u32);
        println!("\\u+{:X}", '\\' as u32);
        println!("{:x}", '\x7F' as u32);
        println!("{:?}", '\"');
        println!("a{}b", '\x08');
        for c in ('\x00'..='\x19').chain('\x0F'..='\x7F') {
            print!("\n\\x{:02x}:\n\t| ab{c}de\n", c as u32);
        }
        // '.'.esc
    }
}
