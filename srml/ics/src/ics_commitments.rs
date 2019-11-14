/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references


/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/srml/example/src/lib.rs

use super::ics_host::*;
use rstd::result;
use rstd::vec::Vec;


/// TODO
/// A CommitmentState is the full state of the commitment, which will be stored by the manager
pub struct CommitmentState {}

pub type CommitmentRoot = CommitmentState;

pub type CommitmentPath = Vec<u8>;

pub type Prefix = Vec<u8>;

// apply prefix constructs a new commitment path from the arguments. It interprets
// the path argument in the context of the prefix argument.
//
// CONTRACT: provided path string MUST be a well formated path. See ICS24 for
// reference.
pub fn apply_prefix(prefix: &Prefix, path: &Vec<u8>) -> result::Result<Vec<u8>, &'static str> {
    default_path_validator(path)?;
    let mut prefix = prefix.clone();
    if prefix.is_empty() {
        Err("prefix can't be empty")
    } else {
        prefix.extend("/".bytes());
        prefix.extend(path.clone());
        Ok(prefix)
    }
}