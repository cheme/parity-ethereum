
extern crate parity_ethereum;
extern crate ethcore;
use std::mem;
use parity_ethereum::plugin::ParityPlugin;
use parity_ethereum::plugin::ParityPluginJsonChain;
use parity_ethereum::plugin::PluginJsonChain;

use ethcore::spec::{Spec, SpecParams};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Musicoin(pub usize); // with a field for test

impl ParityPlugin for Musicoin {

  /// associated chain name
  fn get_name (&self) -> &'static str {
    println!("in get_name");
    "dyn_musicoin"
  }
}
impl ParityPluginJsonChain for Musicoin {

  fn is_legacy(&self) -> bool {
    println!("In get_legacy");
    true
  }

  /// Create a new Musicoin mainnet chain spec.
  fn get_spec(&self, params : SpecParams ) -> Result<Spec, String> {
    println!("In get_spec bef");
  	let s = Spec::load(params, &include_bytes!("../../ethcore/res/ethereum/musicoin.json")[..]);
    println!("In get_spec aft");
    s
  }

  fn clone_plugin(&self) -> PluginJsonChain {
    println!("In clone Plugin bef");
    let r = PluginJsonChain(Box::new(self.clone()));
    println!("In clone Plugin aft");
    r
  }
}

#[no_mangle]
//pub fn instantiate_json_chain() -> *mut Box<ParityPluginJsonChain> {
pub fn instantiate_json_chain() -> Box<dyn ParityPluginJsonChain> {
//pub fn instantiate_json_chain() -> usize {
//32
    Box::new(Musicoin(0))
    //let r = Box::new(Musicoin(0));
    //Box::into_raw(Box::new(r))
}
