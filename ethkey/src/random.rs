// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

use rand::os::OsRng;
use rand::Rng;
use parity_crypto::secp256k1::Secp256k1;
use parity_crypto::traits::asym::Asym;
use parity_crypto::clear_on_drop::clear::Clear;
use super::{Generator, KeyPair};

/// Randomly generates new keypair, instantiating the RNG each time.
pub struct Random;

impl Generator for Random {
	type Error = ::std::io::Error;

	fn generate(&mut self) -> Result<KeyPair, Self::Error> {
		let mut rng = OsRng::new()?;
		match rng.generate() {
			Ok(pair) => Ok(pair),
			Err(err) => Err(::std::io::Error::new(::std::io::ErrorKind::Other, err.to_string())),
		}
	}
}

impl Generator for OsRng {
	type Error = parity_crypto::Error;

	fn generate(&mut self) -> Result<KeyPair, Self::Error> {
		let mut sec_buf = vec![0; Secp256k1::SECRET_SIZE];
		self.fill_bytes(&mut sec_buf[..]);
		let (sec, publ) = Secp256k1::keypair_from_slice(&mut sec_buf)?;
		Clear::clear(&mut sec_buf[..]);

		Ok(KeyPair::from_keypair(sec, publ))
	}
}
