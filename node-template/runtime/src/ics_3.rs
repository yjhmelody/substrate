/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references


/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/srml/example/src/lib.rs

use support::{decl_module, decl_storage, decl_event, dispatch::Result};
use system::ensure_signed;
use super::ics_24::*;
use rstd::result;
use rstd::vec::Vec;

pub trait Trait: system::Trait {
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}


// TODO:
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

// ApplyPrefix constructs a new commitment path from the arguments. It interprets
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

decl_storage! {
	trait Store for Module<T: Trait> as TemplateModule {
		Something get(fn something): Option<u32>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		pub fn do_something(origin, something: u32) -> Result {
			let who = ensure_signed(origin)?;

			Something::put(something);

			Self::deposit_event(RawEvent::SomethingStored(something, who));
			Ok(())
		}
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		SomethingStored(u32, AccountId),
	}
);

#[cfg(test)]
mod tests {
    use super::*;

    use primitives::H256;
    use support::{impl_outer_origin, assert_ok, parameter_types};
    use sr_primitives::{
        traits::{BlakeTwo256, IdentityLookup}, testing::Header, weights::Weight, Perbill,
    };

    impl_outer_origin! {
		pub enum Origin for Test {}
	}

    // For testing the module, we construct most of a mock runtime. This means
    // first constructing a configuration type (`Test`) which `impl`s each of the
    // configuration traits of modules we want to use.
    #[derive(Clone, Eq, PartialEq)]
    pub struct Test;
    parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
	}
    impl system::Trait for Test {
        type Origin = Origin;
        type Call = ();
        type Index = u64;
        type BlockNumber = u64;
        type Hash = H256;
        type Hashing = BlakeTwo256;
        type AccountId = u64;
        type Lookup = IdentityLookup<Self::AccountId>;
        type Header = Header;
        type Event = ();
        type BlockHashCount = BlockHashCount;
        type MaximumBlockWeight = MaximumBlockWeight;
        type MaximumBlockLength = MaximumBlockLength;
        type AvailableBlockRatio = AvailableBlockRatio;
        type Version = ();
    }
    impl Trait for Test {
        type Event = ();
    }
    type TemplateModule = Module<Test>;

    // This function basically just builds a genesis storage key/value store according to
    // our desired mockup.
    fn new_test_ext() -> runtime_io::TestExternalities {
        system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
    }

    #[test]
    fn it_works_for_default_value() {
        new_test_ext().execute_with(|| {
            // Just a dummy test for the dummy funtion `do_something`
            // calling the `do_something` function with a value 42
            assert_ok!(TemplateModule::do_something(Origin::signed(1), 42));
            // asserting that the stored value is equal to what we stored
            assert_eq!(TemplateModule::something(), Some(42));
        });
    }
}
