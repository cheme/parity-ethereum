/// Experimental plugin module
/// first step is not plugin but grouping all interaction from ext chain under a single trait
/// implementation.
///
mod musicoin;
mod callisto;

use engines::{EthEngine};
use ethcore::spec::{Spec, SpecParams};
use parking_lot::Mutex;
use std::fmt::{ Debug, Formatter, Result as FmtResult };
use std::ops::{ Deref, DerefMut };
pub struct Plugin(Box<dyn ParityPlugin>);

impl Deref for Plugin {
  type Target = Box<dyn ParityPlugin>;
  fn deref(&self) -> &Box<dyn ParityPlugin> {
    &self.0
  }
}
impl DerefMut for Plugin {
  fn deref_mut(&mut self) -> &mut Box<dyn ParityPlugin> {
    &mut self.0
  }
}

impl PartialEq for Plugin {
  fn eq(&self, other: &Plugin) -> bool {
    self.same_plugin(other)
  }
}

impl Debug for Plugin {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    self.get_name().fmt(f)
  }
}

impl Clone for Plugin {
  fn clone(&self) -> Plugin {
    self.clone_plugin()
  }
}
pub struct Plugins {
  plugins : Vec<Plugin>,
}

impl Plugins {
  pub fn new() -> Plugins {
    let mut plugins : Vec<Plugin> = Vec::new();
    plugins.push(Plugin(Box::new(musicoin::Musicoin)));
    Plugins {
      plugins : plugins,
    }
  }
  pub fn has_plugin(&self, name : &str) -> bool {
    self.plugins.iter().any(|p| p.get_name() == name)
  }

  pub fn get_plugin(&self, name : &str) -> Option<&Plugin> {
    self.plugins.iter().find(|p| p.get_name() == name)
  }
  pub fn list_plugins(&self) -> String {
    // TODO redo method with cache in Plugins struct
    let mut res = String::new();
    for p in self.plugins.iter(){
      res.push_str(p.get_name());
      res.push_str(", ");
    }
    let n_end = res.len() - 2;
    res.truncate(n_end);

    res
  }


}

/// for now stateless plugin that will be clone to reduce need to sync
/// Might need to have another type that is sync if trait require to keep a state
/// Note that a subtrait would be good ( with no &self in parameter) and make this one private
pub trait ParityPlugin : Send + Debug {

  /// associated chain name
  fn get_name(&self) -> &'static str;
  fn is_legacy(&self) -> bool;
  fn get_legacy_fork_name(&self) -> Option<String> { 
    if self.is_legacy() { Some(self.get_name().to_string()) } else { None }
  }
  fn clone_plugin(&self) -> Plugin;
  fn get_spec(&self, params : SpecParams ) -> Result<Spec, String>;
  fn same_plugin(&self, o : &Plugin) -> bool {
    self.get_name() == o.get_name()
  }
  fn overload_engine(&self, engine : Arc<EthEngine>) -> Arc<EthEngine> {
    engine
  }
}


lazy_static! {
  // contract addresses.
  pub static ref PLUGINS: Mutex<Plugins> = Mutex::new(Plugins::new());
}


