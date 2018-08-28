/// Experimental plugin module
/// first step is not plugin but grouping all interaction from ext chain under a single trait
/// implementation.
///
///
#[cfg(any(not(feature="no-default"),feature="musicoin"))]
mod musicoin;
#[cfg(any(not(feature="no-default"),feature="callisto"))]
mod callisto;

use ethcore::spec::{Spec, SpecParams};
use parking_lot::Mutex;
use std::fmt::{ Debug, Formatter, Result as FmtResult };
use std::ops::{ Deref, DerefMut };

pub struct PluginJsonChain(pub Box<dyn ParityPluginJsonChain>);

impl Deref for PluginJsonChain {
  type Target = Box<dyn ParityPluginJsonChain>;
  fn deref(&self) -> &Box<dyn ParityPluginJsonChain> {
    &self.0
  }
}

impl ParityPlugin for PluginJsonChain {
  fn get_name(&self) -> &'static str {
    self.0.get_name()
  }
}

impl DerefMut for PluginJsonChain {
  fn deref_mut(&mut self) -> &mut Box<dyn ParityPluginJsonChain> {
    &mut self.0
  }
}

impl PartialEq for PluginJsonChain {
  fn eq(&self, other: &PluginJsonChain) -> bool {
    same_plugin(self, other)
  }
}

impl Debug for PluginJsonChain {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    self.get_name().fmt(f)
  }
}

impl Clone for PluginJsonChain {
  fn clone(&self) -> PluginJsonChain {
    self.clone_plugin()
  }
}
pub struct Plugins<P> {
  plugins : Vec<P>,
}

impl<P : ParityPlugin> Plugins<P> {
  pub fn has_plugin(&self, name : &str) -> bool {
    self.plugins.iter().any(|p| p.get_name() == name)
  }

  pub fn get_plugin(&self, name : &str) -> Option<&P> {
    self.plugins.iter().find(|p| p.get_name() == name)
  }
  pub fn list_plugins(&self) -> String {
    // TODO redo method with cache in Plugins struct
    let mut res = String::new();
    for p in self.plugins.iter(){
      res.push_str(p.get_name());
      res.push_str(", ");
    }
    if res.len() > 2 {
      let n_end = res.len() - 2;
      res.truncate(n_end);
    }

    res
  }
}

impl Plugins<PluginJsonChain> {
  pub fn new() -> Plugins<PluginJsonChain> {
    let mut plugins : Vec<PluginJsonChain> = Vec::new();

    #[cfg(any(not(feature="no-default"),feature="musicoin"))]
    plugins.push(PluginJsonChain(Box::new(musicoin::Musicoin)));
    #[cfg(any(not(feature="no-default"),feature="callisto"))]
    plugins.push(PluginJsonChain(Box::new(callisto::Callisto::new())));
    Plugins {
      plugins : plugins,
    }
  }
}

/// Stateless plugin that will be clone to reduce need to sync.
/// For a statefull one, it is up to the implementor to embed it in a clonable sync struct in an
/// Arc.
pub trait ParityPlugin : Send + Debug {
  /// associated chain name
  fn get_name(&self) -> &'static str;
}
fn same_plugin<P1 : ParityPlugin, P2 : ParityPlugin> (p1 : &P1, p2 : &P2 ) -> bool {
    p1.get_name() == p2.get_name()
}

/// This plugin address only the inclusion of a json chain description
/// TODO change wording and rename clone_plugin to `new_handle` or something like that
pub trait ParityPluginJsonChain : ParityPlugin {
  fn clone_plugin(&self) -> PluginJsonChain;
  fn is_legacy(&self) -> bool;
  fn get_legacy_fork_name(&self) -> Option<String> { 
    if self.is_legacy() { Some(self.get_name().to_string()) } else { None }
  }
  fn get_spec(&self, params : SpecParams ) -> Result<Spec, String>;
}

lazy_static! {
  // contract addresses.
  pub static ref PLUGINS_JSON_CHAIN: Mutex<Plugins<PluginJsonChain>> = Mutex::new(Plugins::new());
}


