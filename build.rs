extern crate toml;
use std::env;
use std::fs;
use std::path::Path;
use toml::{ Value};
use std::io::Read;

fn main() {
	if let Ok(spec_path) = env::var("PARITY_BUILD_FROM_SPEC") {
    if spec_path.len() > 0 {
    println!("cargo:rustc-cfg=feature=\"no-default\"");

    let mut file = fs::File::open(&spec_path).expect("File not found at env var PARITY_BUILD_FROM_SPEC");
  	let mut config = String::new();
  	file.read_to_string(&mut config).expect("error reading file");
    // TODO if using this compilation mechanism move eth  parse to its own crate to avoid code duplicate here
    // TODO also probably need to parse chain spec (for engine...)
		let conf : Value = config.parse().expect("Invalid toml config");
		let chain_name = conf["parity"]["chain"].as_str().expect("no chain name");

    if chain_name.starts_with("dyn_") { // TODO add a dyn flag in toml
      let chain_name = &chain_name[4..];
      // TODO proper dyn lib path management (at least some env variable & default linux path). For
      // now hard coded in pulgin code (at least put in env variable)
    } else { 
      println!("cargo:rustc-cfg=feature=\"{}\"",chain_name);
    }
    }
  }
}
