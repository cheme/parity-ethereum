
use super::ParityPlugin;
use super::Plugin;
use std::io::Read;

use ethcore::spec::{ Spec, SpecParams };

use ethereum_types::{ U256, Address };

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Callisto {
  /// Callisto transition block
	pub callisto_transition: u64,
	/// Callisto Treasury Address
	pub callisto_treasury_address: Address,
	/// Callisto Treasury reward
	pub callisto_treasury_reward: U256,
	/// Callisto Stake Address
	pub callisto_stake_address: Address,
	/// Callisto Stake reward
	pub callisto_stake_reward: U256,
}

impl Callisto {
  // dummy value (should be in separate logic loaded from another json or else)
  pub fn new() -> Callisto {
    Callisto {
      callisto_transition : 0,
      callisto_treasury_address : Address::default(),
	    callisto_treasury_reward: U256::default(),
      callisto_stake_address : Address::default(),
	    callisto_stake_reward: U256::default(),
    }
  }

}

impl ParityPlugin for Callisto {

  /// associated chain name
  fn get_name (&self) -> &'static str {
    "callisto"
  }

  fn is_legacy(&self) -> bool {
    true
  }

  /// Create a new Musicoin mainnet chain spec.
  fn get_spec(&self, params : SpecParams ) -> Result<Spec, String> {
    Spec::load(params, &include_bytes!("../../ethcore/res/ethereum/callisto.json")[..])
  }

  fn clone_plugin(&self) -> Plugin {
    Plugin(Box::new(self.clone()))
  }
}

/*
pub mod engine {


pub struct CallistoEngine<E> (E);

impl<M, E:  Engine<M>> Engine<M> for CalistoEngine<E> {
	fn name(&self) -> &str { self.0.name() }
	fn machine(&self) -> &M { self.0.machine() }

	fn seal_fields(&self, header: &Header) -> usize { self.0.seal_fields(header) }

	fn extra_info(&self, header: &Header) -> BTreeMap<String, String> {
    self.0.extra_info(header)
	}

	fn maximum_uncle_count(&self, block: BlockNumber) -> usize { 
    self.0.maximum_uncle_count(block)
  }

	fn populate_from_parent(&self, header: &mut Header, parent: &Header) {
    self.0.populate_from_parent(header,parent)
	}

	fn on_close_block(&self, block: &mut ExecutedBlock) -> Result<(), Error> {
    self.0.on_close_block(block)
	}

	fn verify_local_seal(&self, header: &Header) -> Result<(), Error> {
    self.0.verify_local_seal(header)
	}

	fn verify_block_basic(&self, header: &Header) -> Result<(), Error> {
    self.0.verify_block_basic(header
	}

	fn verify_block_unordered(&self, header: &Header) -> Result<(), Error> {
    self.0.verify_block_unordered(header)
	}

	fn verify_block_family(&self, header: &Header, parent: &Header) -> Result<(), Error> {
    self.0.verify_block_family(header,parent)
	}

	fn epoch_verifier<'a>(&self, header: &Header, proof: &'a [u8]) -> engines::ConstructedVerifier<'a, M> {
    self.0.epoch_verifier(header,proof)
	}

	fn snapshot_components(&self) -> Option<Box<::snapshot::SnapshotComponents>> {
    self.0.snapshot_components()
	}

	fn fork_choice(&self, new: &ExtendedHeader, current: &ExtendedHeader) -> engines::ForkChoice {
    self.0.fork_choice()
	}
}


}*/
