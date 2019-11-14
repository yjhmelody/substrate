/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references


/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/srml/example/src/lib.rs

use support::{decl_module, decl_storage, decl_event, dispatch::Result};
use system::ensure_signed;
use super::ics_host::*;
use rstd::result;
use rstd::vec::Vec;

/// A CommitmentState is the full state of the commitment, which will be stored by the manager
pub struct CommitmentState {}

type CommitmentRoot = CommitmentState;

type CommitmentPath = Vec<u8>;

pub trait Prefix {
    fn into_bytes(self) -> Vec<u8>;
}

impl Prefix for Vec<u8> {
    fn into_bytes(self) -> Vec<u8> {
        self
    }
}

// apply prefix constructs a new commitment path from the arguments. It interprets
// the path argument in the context of the prefix argument.
//
// CONTRACT: provided path string MUST be a well formated path. See ICS24 for
// reference.
pub fn apply_prefix<P: Prefix>(prefix: P, path: &Vec<u8>) -> result::Result<Vec<u8>, &'static str> {
    default_path_validator(path)?;

    let mut prefix = prefix.into_bytes();
    if prefix.len() == 0 {
        Err("prefix can't be empty")
    } else {
        prefix.extend("/".bytes());
        prefix.extend(path.clone());
        Ok(prefix)
    }
}