extern crate toml;
use std::env;
use std::fs;
use std::path::Path;
use toml::{ Value};
use std::io::Read;

fn main() {
	if let Ok(spec_path) = env::var("PARITY_BUILD_FROM_SPEC") {
    println!("cargo:rustc-cfg=feature=\"no-default\"");

    let mut file = fs::File::open(&spec_path).expect("File not found at env var PARITY_BUILD_FROM_SPEC");
  	let mut config = String::new();
  	file.read_to_string(&mut config).expect("error reading file");
    // TODO if using this compilation mechanism move eth  parse to its own crate to avoid code duplicate here
    // TODO also probably need to parse chain spec (for engine...)
		let conf : Value = config.parse().expect("Invalid toml config");
		let chain_name = conf["parity"]["chain"].as_str().expect("no chain name");
    println!("cargo:rustc-cfg=feature=\"{}\"",chain_name);
  }
}
