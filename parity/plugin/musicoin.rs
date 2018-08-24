
use super::ParityPlugin;
use super::Plugin;
use std::io::Read;

use ethcore::spec::{Spec, SpecParams};
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Musicoin;

impl ParityPlugin for Musicoin {

  /// associated chain name
  fn get_name (&self) -> &'static str {
    "musicoin"
  }

  fn is_legacy(&self) -> bool {
    true
  }

  /// Create a new Musicoin mainnet chain spec.
  fn get_spec(&self, params : SpecParams ) -> Result<Spec, String> {
  	Spec::load(params, &include_bytes!("../../ethcore/res/ethereum/musicoin.json")[..])
  }

  fn clone_plugin(&self) -> Plugin {
    Plugin(Box::new(self.clone()))
  }
}


