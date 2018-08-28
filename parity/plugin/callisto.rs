
use super::ParityPlugin;
use super::ParityPluginJsonChain;
use super::PluginJsonChain;


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

}

impl ParityPluginJsonChain for Callisto {

  fn is_legacy(&self) -> bool {
    true
  }

  /// Create a new Musicoin mainnet chain spec.
  fn get_spec(&self, params : SpecParams ) -> Result<Spec, String> {
    Spec::load(params, &include_bytes!("../../ethcore/res/ethereum/callisto.json")[..])
  }

  fn clone_plugin(&self) -> PluginJsonChain {
    PluginJsonChain(Box::new(self.clone()))
  }
}
