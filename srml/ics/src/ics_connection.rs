use support::{decl_module, decl_storage, decl_event, dispatch::{Result, Parameter}};
use system::ensure_signed;
use rstd::prelude::*;
use codec::{Decode, Encode};
use rstd::vec::Vec;
use sr_primitives::traits::{Member, MaybeSerializeDeserialize, MaybeDisplay};

use crate::ics_host::*;

pub trait Trait: system::Trait {
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum ConnectionState {
	None = 0,
	Init = 1,
	TryOpen = 2,
	Open = 3,
}

pub type ConnectionId = Vec<u8>;
pub type ClientId = Vec<u8>;
pub type ConnectionPath = Vec<u8>;

#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ConnectionEnd {
	state: ConnectionState,
	client_id: ClientId,
	counterparty: Counterparty,
	versions: Vec<Vec<u8>>,
}

fn get_compatible_versions() -> Vec<Vec<u8>> {
	vec![b"1.0.0".to_vec()]
}

impl ConnectionEnd {
	pub fn new(state: ConnectionState, client_id: ClientId, counterparty: Counterparty, versions: Vec<Vec<u8>>) -> Self {
		Self {
			state,
			client_id,
			counterparty,
			versions,
		}
	}
}

#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Counterparty {
	client_id: ClientId,
	connection_id: ConnectionId,
	prefix: Vec<u8>,
}

impl Counterparty {
	pub fn new(client_id: ClientId, connection_id: ConnectionId, prefix: Vec<u8>) -> Self {
		Self {
			client_id,
			connection_id,
			prefix,
		}
	}

	pub fn validate_basic(&self) -> Result {
		default_connection_identifier_validator(&self.connection_id)?;
		default_client_identifier_validator(&self.client_id)?;
		if self.prefix.is_empty() {
			Err("invalid counterparty prefix")
		} else {
			Ok(())
		}
	}
}

fn connection_path(connection_id: ConnectionId) -> Vec<u8> {
	let mut path = b"connections/".to_vec();
	path.extend(connection_id);
	path
}

fn client_connections_path(client_id: ClientId) -> Vec<u8> {
	let mut path = b"client/".to_vec();
	path.extend(client_id);
	path.extend(b"/connections");
	path
}

#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ConnectionOpenInit<Acc> {
	connection_id: ConnectionId,
	client_id: ClientId,
	counterparty: Counterparty,
	signer: Option<Acc>,
}

impl<Acc> ConnectionOpenInit<Acc>
where Acc: Parameter + Member + MaybeSerializeDeserialize + MaybeDisplay + Ord + Default
{
	pub fn new(connection_id: ConnectionId, client_id: ClientId, counterparty_connection_id: ConnectionId,
		counterparty_client_id: ClientId, counterparty_prefix: Vec<u8>, signer: Option<Acc>,
	) -> Self {
		let counterparty = Counterparty::new(counterparty_client_id, counterparty_connection_id, counterparty_prefix);
		Self {
			connection_id,
			client_id,
			counterparty,
			signer,
		}
	}

	pub fn validate_basic(&self) -> Result {
		default_connection_identifier_validator(&self.connection_id)?;
		default_client_identifier_validator(&self.client_id)?;
		self.signer.as_ref().ok_or("missing signer address")?;
		self.counterparty.validate_basic()
	}
}

//#[derive(Clone, Encode, Decode)]
//#[cfg_attr(feature = "std", derive(Debug))]
//pub struct ConnectionOpenTry<Acc> {
//	connection_id: ConnectionId,
//	client_id: ClientId,
//	counterparty: Counterparty,
//	counterparty_versions: Vec<Vec<u8>>,
//	proof_init:
//}


decl_storage! {
	trait Store for Module<T: Trait> as IcsConnections {
		Something get(fn something): Option<u32>;

		/// sets the connections paths for client
		Connections get(connections): map Vec<u8> => Option<Vec<Vec<u8>>>;

		/// GetConnection returns a connection with a particular identifier
		ConnectionEnds get(connection_ends): map ConnectionId => Option<ConnectionEnd>;
	}
}

impl<T: Trait> Module<T> {
	// add a connection identifier to the set of connections associated with a client.
	fn add_connection_to_client(client_id: ClientId, connection_id: ConnectionId) -> Result {
		let path = client_connections_path(client_id);

		let mut conns: Vec<Vec<u8>> = match Self::connections(path.clone()) {
			Some(conns) => conns,
			None => vec![],
		};
		conns.push(connection_id);
		<Connections>::insert(path, conns);

		Ok(())
	}

	// remove a connection identifier from the set of connections associated with a client
	fn remove_connection_from_client(client_id: ClientId, connection_id: ConnectionId) -> Result {
		let path = client_connections_path(client_id);

		let conns: Vec<Vec<u8>> = match Self::connections(path.clone()) {
			Some(conns) => conns,
			None => return Ok(()),
		};

		let mut new_conns = vec![];

		for conn in conns {
			if conn != path {
				new_conns.push(conn);
			}
		}

		<Connections>::insert(path, new_conns);

		Ok(())
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

		// ConnOpenInit initialises a connection attempt on chain A.
		//
		// NOTE: Identifiers are checked on msg validation.
		pub fn conn_open_init(origin, connection_id: ConnectionId, client_id: ClientId, counterparty: Counterparty) -> Result {
			if Self::connection_ends(connection_id.clone()).is_some() {
				return Err("cannot initialize connection");
			}
			let connection = ConnectionEnd::new(ConnectionState::Init, client_id.clone(), counterparty, get_compatible_versions());

			<ConnectionEnds>::insert(connection_id.clone(), connection);
			Self::add_connection_to_client(client_id, connection_id);

			Ok(())
		}

		// ConnOpenTry relays notice of a connection attempt on chain A to chain B (this
		// code is executed on chain B).
		//
		// NOTE:
		//  - Here chain A acts as the counterparty
		//  - Identifiers are checked on msg validation
		pub fn conn_open_try(origin) -> Result {
			unimplemented!();
		}

		// ConnOpenAck relays acceptance of a connection open attempt from chain B back
		// to chain A (this code is executed on chain A).
		//
		// NOTE: Identifiers are checked on msg validation.
		pub fn conn_open_ack(origin) -> Result {
			unimplemented!();
		}

		// ConnOpenConfirm confirms opening of a connection on chain A to chain B, after
		// which the connection is open on both chains (this code is executed on chain B).
		//
		// NOTE: Identifiers are checked on msg validation.
		pub fn conn_open_confirm(origin) -> Result {
			unimplemented!();
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
