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

use super::{Public, Secret, Error};
use parity_crypto::secp256k1::Secp256k1;
use parity_crypto::traits::asym::{FiniteField, Asym, PublicKey};
use ethereum_types::{U256, H256};

/// Whether the public key is valid.
pub fn public_is_valid(public: &Public) -> bool {
	public.is_valid()
}

/// Inplace multiply public key by secret key (EC point * scalar)
pub fn public_mul_secret(public: &mut Public, secret: &Secret) -> Result<(), Error> {
	let key_secret = secret.to_secp256k1_secret()?;
	Secp256k1::public_mul(public, &key_secret)?;
	Ok(())
}

/// Inplace add one public key to another (EC point + EC point)
pub fn public_add(public: &mut Public, other: &Public) -> Result<(), Error> {
	Secp256k1::public_add(public, other)?;
	Ok(())
}

/// Inplace sub one public key from another (EC point - EC point)
pub fn public_sub(public: &mut Public, other: &Public) -> Result<(), Error> {
	let mut key_neg_other = other.clone();
	Secp256k1::public_mul(&mut key_neg_other, Secp256k1::minus_one_key())?;

	Secp256k1::public_add(public, &key_neg_other)?;
	Ok(())
}

/// Replace public key with its negation (EC point = - EC point)
pub fn public_negate(public: &mut Public) -> Result<(), Error> {
	Secp256k1::public_mul(public, Secp256k1::minus_one_key())?;
	Ok(())
}

/// Return base point of secp256k1
/// TODO move arith to crypto
pub fn generation_point() -> Public {
	let mut public_sec_raw = [0u8; 64];
	public_sec_raw[0..32].copy_from_slice(Secp256k1::generator_x());
	public_sec_raw[32..64].copy_from_slice(Secp256k1::generator_y());

	Public::from_pub(Secp256k1::public_from_slice(&public_sec_raw)
		.expect("constructing using predefined constants; qed"))
}

/// Return secp256k1 elliptic curve order
pub fn curve_order() -> U256 {
	H256::from_slice(Secp256k1::curve_order()).into()
}

#[cfg(test)]
mod tests {
	use super::super::{Random, Generator};
	use super::{public_add, public_sub};

	#[test]
	fn public_addition_is_commutative() {
		let public1 = Random.generate().unwrap().public().clone();
		let public2 = Random.generate().unwrap().public().clone();

		let mut left = public1.clone();
		public_add(&mut left, &public2).unwrap();

		let mut right = public2.clone();
		public_add(&mut right, &public1).unwrap();

		assert_eq!(left, right);
	}

	#[test]
	fn public_addition_is_reversible_with_subtraction() {
		let public1 = Random.generate().unwrap().public().clone();
		let public2 = Random.generate().unwrap().public().clone();

		let mut sum = public1.clone();
		public_add(&mut sum, &public2).unwrap();
		public_sub(&mut sum, &public2).unwrap();

		assert_eq!(sum, public1);
	}
}
