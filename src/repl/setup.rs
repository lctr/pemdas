use std::{
    fs, io,
    path::{Path, PathBuf},
};

const LOCAL_HISTORY_FILE: &'static str = ".pemdas_history";
const GLOBAL_HISTORY_FILE: &'static str = ".history";

pub fn try_cfg_dir() -> io::Result<PathBuf> {
    if let Some(home) = std::option_env!("HOME") {
        let path = PathBuf::from(home);
        let pemdas_dir = path.join(".pemdas");
        if pemdas_dir.exists() {
            if pemdas_dir.is_dir() {
                Ok(pemdas_dir)
            } else {
                eprintln!("`/.pemdas` exists but is not a directory!");
                eprintln!("defaulting to current directory");
                Ok(PathBuf::from("."))
            }
        } else {
            fs::create_dir(&pemdas_dir)?;
            Ok(pemdas_dir)
        }
    } else {
        eprintln!("environment variable HOME is not set");
        eprintln!("defaulting to current directory");
        Ok(PathBuf::from("."))
    }
}

pub type HistoryPath = PathBuf;

pub fn try_history_path() -> io::Result<HistoryPath> {
    match try_cfg_dir() {
        Ok(pemdas_dir) => {
            let history_path = pemdas_dir.join(GLOBAL_HISTORY_FILE);
            if history_path.exists() {
                Ok(history_path)
            } else {
                fs::File::options()
                    .create(true)
                    .write(true)
                    .open(&history_path)?
                    .sync_all()?;
                Ok(history_path)
            }
        }
        Err(e) => Err(e),
    }
}

#[allow(unused)]
fn uninstall_artifacts(p: impl AsRef<Path>) {
    let path = p.as_ref();
    let history_file_name = if path.canonicalize().and_then(|pc| PathBuf::from(".").canonicalize().map(|cwd| cwd == pc)
    ).unwrap_or_else(|e| {
        eprintln!("Error canonicalizing `{}` and `.` for comparison while identifying history file name to delete: {}", path.display(), e);
        false
    }) {
        LOCAL_HISTORY_FILE
    } else {
        GLOBAL_HISTORY_FILE
    };
    // let mut deleted_history_file = false;
    match fs::read_dir(path) {
        Ok(rd) => {
            for de in rd.flatten() {
                if de.file_name() == history_file_name {
                    if de.path().exists() {
                        eprintln!("deleting history file found at {}", de.path().display());
                        fs::remove_file(de.path()).unwrap();
                        // deleted_history_file = true;
                    }
                }
            }
            if let Ok(n) = fs::read_dir(path).map(|rd| rd.fold(0, |a, _c| a + 1)) {
                let global = history_file_name == GLOBAL_HISTORY_FILE;
                if n == 0 && global {
                    fs::remove_dir_all(path).unwrap();
                } else {
                    eprintln!("could not delete non-empty directory `{}`", path.display())
                }
            }
        }
        Err(e) => eprintln!(
            "Error calling `uninstall_artifacts({})`: {}",
            path.display(),
            e
        ),
    }
}
