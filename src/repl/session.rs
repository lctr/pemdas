use rustyline::error::ReadlineError;

use crate::syntax::{
    ast::{Ast, Decl, Expr, Infix},
    fixity::{self, FixityEntries, Resolver},
    parser,
};

use crate::text::{grapheme::is_prefix, style::Paint};

use super::setup::{self, HistoryPath};

static VERSION: &'static str = "0.1.0";

#[derive(Debug)]
pub enum Error {
    Parser(parser::Error),
    Resolver(Vec<fixity::AssocError>),
}

impl Error {
    #[inline]
    pub fn print_with_path(&self, p: impl AsRef<std::path::Path>) {
        struct Show<'a>(&'a Error, &'a std::path::Path);
        impl std::fmt::Display for Show<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                self.0.write_with_path(self.1, f)
            }
        }
        println!("{}", Show(&self, p.as_ref()))
    }

    pub fn write_with_path(
        &self,
        p: impl AsRef<std::path::Path>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        "[Error]:".set_fg_red().fresh_suffix(" ").display_fmt(f)?;
        let p = p.as_ref();
        let at_path = "(".set_fg_blue().append(p.display());
        match self {
            Error::Parser(e) => {
                write!(f, " ")?;
                at_path
                    .append(":")
                    .append(e.loc().line)
                    .append(":")
                    .append(e.loc().col)
                    .append(") ")
                    .fmt_display(f)?;
                e.write_without_loc(f)
            }
            Error::Resolver(errs) => {
                at_path.append(")").fmt_display(f)?;
                for e in errs {
                    write!(f, "\n  {e}")?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        crate::text::style::Style::new("[Error]:")
            .set_fg_red()
            .fresh_suffix(" ")
            .styled()
            .fmt_display(f)?;
        match self {
            Error::Parser(e) => write!(f, "{e}"),
            Error::Resolver(errs) => {
                match &errs[..] {
                    [] => (),
                    [e] => {
                        write!(f, "{e}")?;
                    }
                    [es @ ..] => {
                        for e in es {
                            write!(f, "\n  {e}")?;
                        }
                    }
                }
                Ok(())
            }
        }
    }
}

// const BLUE_PROMPT_IN: &'static str = "\u{1b}[34m> \u{1b}[0m";
const GREEN_PROMPT_IN: &'static str = "\u{1b}[32m> \u{1b}[0m";
const BLUE_PROMPT_CONT: &'static str = "\u{1b}[34m |  \u{1b}[0m";

#[derive(Clone, Copy, PartialEq)]
#[default_variant::default(Initial)]
enum LinePrompt {
    Initial,
    Continued,
}

impl LinePrompt {
    #[inline]
    fn reset(&mut self) {
        *self = Self::Initial;
    }

    #[inline]
    fn cont_line(&mut self) {
        *self = Self::Continued;
    }

    #[inline]
    fn is_continued(&self) -> bool {
        matches!(self, Self::Continued)
    }

    #[inline]
    fn as_str(&self) -> &'static str {
        match self {
            LinePrompt::Initial => GREEN_PROMPT_IN,
            LinePrompt::Continued => BLUE_PROMPT_CONT,
        }
    }
}

pub struct ReplSession {
    resolver: Resolver,
    buffer: String,
    prompt: LinePrompt,
    history_path: HistoryPath,
}

impl Default for ReplSession {
    fn default() -> Self {
        Self {
            resolver: Default::default(),
            buffer: Default::default(),
            prompt: LinePrompt::default(),
            history_path: setup::try_history_path().unwrap_or_default(),
        }
    }
}

impl ReplSession {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn print_init_msg(&self) {
        println!("Pemdas, version {}", VERSION);
        println!("history stored at \"{}\"", &self.history_path.display());
        println!(
            "{}",
            "    :quit, :q               \
            exit REPL\
            \n    :fixities               \
            display the fixities of infixes \
            defined in session\
            \n    :help, :h               \
            display list of REPL commands"
        )
    }

    fn prompt_str(&self) -> &str {
        self.prompt.as_str()
    }

    pub fn feed_input(&mut self, input: &str) -> Result<Ast, Error> {
        match parser::parse(input) {
            Ok(mut ast) => self
                .resolver
                .load_fixities(&mut ast)
                .resolve_ast(&mut ast)
                .map(|_| ast)
                .map_err(Error::Resolver),
            Err(e) => Err(Error::Parser(e)),
        }
    }

    fn read_buffer(&mut self) {
        let input = self.take_buffer();
        match self.feed_input(&*input) {
            Ok(ast) => match ast.iter().next() {
                Some(decl) => match decl {
                    Decl::Expr(expr) => {
                        self.print_expr(&expr.expr);
                    }
                    _ => (),
                },
                None => (),
            },
            Err(e) => eprintln!("{e}"),
        }
    }

    fn read_file(&mut self, p: impl AsRef<std::path::Path>) {
        let p = p.as_ref().to_path_buf();
        let is_hs_file = p.extension().map(|s| s == "hs").unwrap_or_else(|| false);
        match std::fs::read_to_string(&p) {
            Ok(s) => {
                match self.feed_input(
                    &(if !is_hs_file {
                        s
                    } else {
                        s.lines()
                            .filter_map(|line| {
                                let line = line.trim();
                                if line.starts_with("infix") {
                                    Some(line)
                                } else {
                                    None
                                }
                            })
                            .collect::<String>()
                    }),
                ) {
                    Ok(ast) => {
                        println!("{} fixities read from `{}`", ast.infxs.len(), p.display());
                        FixityEntries::from_iter(
                            ast.infxs
                                .iter()
                                .flat_map(|infx| infx.infixes.iter().map(|op| (op, &infx.fixity))),
                        )
                        .print_fixities();
                    }
                    Err(e) => e.print_with_path(p),
                }
            }
            Err(e) => {
                eprintln!("unable to read `{}`", p.display());
                eprintln!("{}", e.kind());
            }
        }
    }

    pub fn print_expr(&self, expr: &Expr) {
        self.resolver.print_expr(expr)
    }

    pub fn buffer_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    pub fn take_buffer(&mut self) -> String {
        std::mem::take(&mut self.buffer)
    }
}

pub fn run_repl() {
    let mut rl = rustyline::Editor::<()>::with_config(
        rustyline::Config::builder()
            .auto_add_history(true)
            .max_history_size(100)
            .tab_stop(4)
            .build(),
    )
    .unwrap();
    let mut sess = ReplSession::new();
    let _ = rl.load_history(&sess.history_path);
    sess.print_init_msg();
    loop {
        match rl.readline(sess.prompt_str()) {
            Err(err) => match err {
                ReadlineError::Eof | ReadlineError::Interrupted => break,
                e => eprintln!("Error: {e}"),
            },
            Ok(line) => {
                match line.trim() {
                    "" => continue,
                    s if s.trim().starts_with(":") => {
                        if sess.buffer_empty() {
                            if read_command(&mut sess, &mut rl, s) {
                                continue;
                            } else {
                                break;
                            }
                        } else {
                            eprintln!("cannot call a command in multiline mode!");
                            continue;
                        }
                    }
                    s if {
                        let s = s.trim();
                        (s.starts_with("infix")
                            || s.starts_with("infixl")
                            || s.starts_with("infixr"))
                            && s.ends_with(" \\")
                    } =>
                    {
                        sess.buffer.push_str(&s[0..s.len() - " \\".len()]);
                        sess.buffer.push_str("\n");
                        sess.prompt.reset();
                        continue;
                    }
                    s if s.ends_with('\\') => {
                        sess.buffer.push_str(&s[0..s.len() - '\\'.len_utf8()]);
                        sess.buffer.push_str("\n ");
                        sess.prompt.reset();
                        continue;
                    }
                    s if s.starts_with('{') => {
                        let s = s.trim_start_matches('{');
                        if !s.ends_with('}') {
                            sess.prompt.cont_line();
                            sess.buffer.push_str(s);
                            continue;
                        }
                        sess.buffer.push_str(s.trim_end_matches('}'));
                    }
                    s => {
                        sess.buffer.push_str(s);
                        if sess.prompt.is_continued() {
                            sess.prompt.reset();
                        }
                    }
                };

                sess.read_buffer()
            }
        }
    }
}

pub const HELP_MSG: &'static str = r#"Pemdas commands:
    :cd <path>?             change the current working directory to the
                            given path
    :clear
        --fixities          clear all fixities for the current session
        --history           clear the history for the current session
        --session           clear all fixities and history for the current
                            session (equivalent to using the options
                            `--fixities history` or `--history --fixities`)
    :fixities               display the fixities of infixes defined in session
    :help, :h, :?           display this list of commands
    :history
        --clear             clear the history for the current session
        --clear --file      clear the history along with the contents of the
                            history file for the current session
        --set <path>        set the path to which this session's history will
                            be saved (non-existent files will be created)
        --save [<path>]     saves the current session history in the file
                            located at <path>
    :info, :i [<infix>]     display the fixity of the given infixes
                            (same as `:fixities` if no infixes are provided)
                            * note that as inputs, promoted infixes
                              should not contain the apostrophe prefix or
                              backtick circumfix even though the printed
                              outputs may contain them
    :load
        --prelude           load the same fixities as those defined in the
                            Haskell prelude
        --math              load the fixities for the arithmetic operators
                            +, -, *, /, %, ^, ^^, and **
        <path>+             load and process the file associated with the
                            given path(s), bringing in to scope any defined
                            fixities
                            * files may end in any file-extension
                            * if any file is a Haskell module (i.e., has a
                              `.hs` file extension), then only fixities that
                              were declared at the top-level are processed
                              (e.g., imports and fixity declarations in class
                              declarations or in let-expressions may be
                              ignored)
    :quit, :q               exit Pemdas
        --no-history        exit Pemdas without saving history
    :reset, :r              shortcut for `:clear --fixities`: reset the
                            fixities defined in the current session
    :save <path>            save the fixities of this session as a list of
                            fixity declarations to the file located at <path>
        --append            * append declarations to file instead of
                              overwriting file if file at <path> exists
    :shell
        <program> <args>*   spawn a child process and run the given input
                            as the program
"#;

fn read_command(sess: &mut ReplSession, rl: &mut rustyline::Editor<()>, input: &str) -> bool {
    match input.trim() {
        s if is_prefix(":cd", s) => {
            let p = s[":cd".len()..].trim();
            if p.is_empty() {
                eprintln!("no directory provided to `:cd` command")
            } else {
                if let Err(e) = std::env::set_current_dir(p) {
                    eprintln!(
                        "could not change current directory to `{}`: {}",
                        p,
                        e.kind()
                    );
                }
            }
        }
        ":help" | ":h" | ":?" => {
            println!("{}", HELP_MSG);
        }
        s if is_prefix(":q", s) || is_prefix(":quit", s) => {
            let save_history = match s {
                ":quit" | ":q" => true,
                ":quit --no-history" | ":q --no-history" => false,
                s => {
                    eprintln!("unknown command: `{}`", s);
                    return true;
                }
            };
            if save_history {
                let _ = rl.save_history(&sess.history_path);
            }
            println!("exiting Pemdas REPL");
            return false;
        }
        s if is_prefix(":clear", s) => {
            let s = s[":clear".len()..].trim();
            match s {
                "--history" => {
                    rl.clear_history();
                    println!("session history cleared")
                }
                "--fixities" => {
                    println!("{} fixities cleared", sess.resolver.clear())
                }
                "--session" | "--history --fixities" | "--fixities --history" => {
                    let k = sess.resolver.clear();
                    rl.clear_history();
                    println!("{k} fixities cleared, session history cleared")
                }
                s => {
                    eprintln!("unknown option(s) passed to command `:clear`: {s}");
                }
            }
        }
        s if is_prefix(":history", s) => {
            let s = s[":history".len()..].trim();
            match s {
                "--clear" => {
                    rl.clear_history();
                    println!("session history cleared")
                }
                "--clear --file" => {
                    rl.clear_history();
                    let _ = rl.save_history(&sess.history_path);
                    println!("session history and file cleared")
                }
                s if s.starts_with("--set") => match s["--set".len()..].trim() {
                    "" => {
                        eprintln!("no filepath provided for command `:history --set`")
                    }
                    p => {
                        sess.history_path = p.into();
                        println!(
                            "session history filepath changed to\n  {}",
                            &sess.history_path.display()
                        )
                    }
                },
                s if is_prefix("--save", s) => {
                    let len = s.len();
                    let save = "--save".len();
                    if len == save {
                        let _ = rl.save_history(&sess.history_path);
                    } else {
                        let p = s[save..].trim();
                        let _ = rl.save_history(p);
                    }
                    println!(
                        "session history written to file located at\n  {}",
                        &sess.history_path.display()
                    );
                }
                s => {
                    eprintln!("invalid option/argument to `:history` command: `{}`", s);
                    eprintln!("USAGE:\n  :history --clear\n  :history --set <path>\n  :history --save [<path>]");
                }
            }
        }
        ":reset" | ":r" => {
            let k = sess.resolver.clear().saturating_sub(1);
            println!("{k} fixities removed")
        }
        ":info" | ":i" | ":fixities" => {
            sess.resolver.printer().print_fixities();
        }
        s if is_prefix(":info", s) || is_prefix(":i", s) => {
            let s = if is_prefix(":info", s) {
                &s[":info".len()..]
            } else {
                &s[":i".len()..]
            };
            use crate::text::symbol::Symbol;
            let fixities = sess.resolver.fixities();
            let (defined, undefined): (Vec<_>, Vec<_>) = s
                .replace(|c| c == '(' || c == ')', "")
                .split_whitespace()
                .map(|s| {
                    (if s.starts_with(|c: char| c.is_alphabetic() || c == '_') {
                        Infix::Promoted
                    } else {
                        Infix::Standard
                    })(Symbol::intern(s))
                })
                .partition(|op| fixities.has(op));
            sess.resolver
                .entries_for(defined.into_iter())
                .print_fixities();
            if let [op, ops @ ..] = &undefined[..] {
                print!("the following were not defined: {op}");
                for op in ops {
                    print!(", {op}")
                }
            }
        }
        s if is_prefix(":load", s) => match s[":load".len()..].trim() {
            "" => {
                eprintln!("`:load` command missing option/argument");
            }
            "--prelude" => {
                let k = sess.resolver.load_hs_prelude();
                println!("loaded {k} fixities from Haskell prelude")
            }
            "--math" => {
                let k = sess.resolver.load_arithmetic();
                println!("loaded {k} fixities for arithmetic operators")
            }
            p => p.split_whitespace().for_each(|p| {
                let p = if p.starts_with('"') && p.ends_with('"') {
                    &p['"'.len_utf8()..p.len()]
                } else {
                    p
                };
                sess.read_file(p)
            }),
        },

        s if is_prefix(":shell", s) => {
            let s = &s[":shell".len()..];
            let mut iter = s.split_whitespace();
            if let Some(prog) = iter.next() {
                match std::process::Command::new(prog)
                    .args(iter)
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn()
                {
                    Ok(child) => match child.wait_with_output() {
                        Ok(_out) => {
                            use std::io::Write;
                            let stdout = std::io::stdout();
                            let mut stdout = stdout.lock();
                            let _ = stdout.write_all(&_out.stdout[..]);
                        }
                        Err(e) => eprintln!("{e}"),
                    },
                    Err(e) => {
                        eprintln!("{e}")
                    }
                }
            } else {
                eprintln!("no command provided to `:shell/:sh` command");
                eprintln!("USAGE: :shell CMD <ARG>*")
            }
        }

        s => {
            eprintln!("unknown command: `{}`", s);
            sess.buffer.clear();
        }
    };
    true
}

// pub const ARITHMETIC: &'static str = r#"
// infixl 6 +, -
// infixl 7 *, /, %
// infixr 8 ^, ^^
// "#;

// pub const PRELUDE: &'static str = r#"
// infixr 0 $, $!
// infixl 1 >>=, >>
// infixr 1 =<<
// infixr 2 ||
// infixr 3 &&
// infix  4 ==, /=, <, <=, >, >=
// infixl 4 <*, <*>, *>, <$, <$>
// infixr 5 ++
// infixr 6 <>
// infixl 6 +, -
// infixl 7 *, /, %
// infixr 8 ^, ^^, **
// infixr 9 .
// infixl 9 !!
// "#;

#[cfg(test)]
mod test {
    // use super::*;

    #[test]
    fn history() -> std::io::Result<()> {
        let current_dir = std::env::current_dir()?;
        println!("current_dir: {}", current_dir.display());
        let current_exe = std::env::current_exe()?;
        println!("current_exe: {}", current_exe.display());
        println!("vars\n-------");
        for (key, value) in std::env::vars() {
            println!("{key}: {value}");
        }
        Ok(())
    }
}
