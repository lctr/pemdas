pub mod repl;
pub mod syntax;
pub mod text;

/// TODO: add config options/args? or always go straight to REPL
fn main() {
    repl::run()
}
