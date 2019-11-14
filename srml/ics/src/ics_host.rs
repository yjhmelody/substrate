use support::dispatch::Result;
use rstd::prelude::*;

fn default_identifier_validator(id: &Vec<u8>, min: usize, max: usize) -> Result {
    // valid id must be between 10 and 20 characters
    if id.len() < min || id.len() > max {
        return Err("identifier has invalid length");
    }

    // valid id MUST NOT contain "/" separator
    if id.contains(&b'/') {
        return Err(r"identifier cannot contain separator: /");
    }

    // valid id must contain only lower alphabetic characters
    if !is_ascii_lowercase(id) {
        return Err("identifier must contain only lowercase alphabetic characters");
    }

    Ok(())
}

fn is_ascii_lowercase(id: &Vec<u8>) -> bool {
    id.iter().all()
    for ch in id {
        if !ch.is_ascii_lowercase() {
            return false;
        }
    }

    true
}

// DefaultClientIdentifierValidator is the default validator function for Client identifiers
// A valid Identifier must be between 10-20 characters and only contain lowercase
// alphabetic characters
pub fn default_client_identifier_validator(id: &Vec<u8>) -> Result {
    default_identifier_validator(id, 10, 20)
}

// DefaultConnectionIdentifierValidator is the default validator function for Connection identifiers
// A valid Identifier must be between 10-20 characters and only contain lowercase
// alphabetic characters
pub fn default_connection_identifier_validator(id: &Vec<u8>) -> Result {
    default_identifier_validator(id, 10, 20)
}

// DefaultChannelIdentifierValidator is the default validator function for Channel identifiers
// A valid Identifier must be between 10-20 characters and only contain lowercase
// alphabetic characters
pub fn default_channel_identifier_validator(id: &Vec<u8>) -> Result {
    default_identifier_validator(id, 10, 20)
}

// DefaultPortIdentifierValidator is the default validator function for Port identifiers
// A valid Identifier must be between 2-20 characters and only contain lowercase
// alphabetic characters
pub fn default_port_identifier_validator(id: &Vec<u8>) -> Result {
    default_identifier_validator(id, 2, 20)
}

// DefaultPathValidator takes in path string and validates
// with default identifier rules. This is optimized by simply
// checking that all path elements are alphanumeric
pub fn default_path_validator(path: &Vec<u8>) -> Result {
    let path_vec = path.split(|ch| *ch == b'/').collect::<Vec<_>>();
    for path in path_vec {
        if !is_ascii_lowercase(&path.to_vec()) {
            return Err("invalid path element containing non-alphanumeric characters");
        }
    }

    Ok(())
}
