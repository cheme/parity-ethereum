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

use std::fmt;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;
use std::cmp::Ordering;
use rustc_hex::ToHex;
use parity_crypto::secp256k1::Secp256k1;
use parity_crypto::traits::asym::{Asym, FiniteField};
use ethereum_types::{H256, H512};
use Error;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Secret {
	inner: <Secp256k1 as Asym>::SecretKey,
}

// Note that equal and ord implementation is less efficient than previous FixedHash one (libc
// call).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Public {
	inner: <Secp256k1 as Asym>::PublicKey,
}

lazy_static! {
	static ref DEFAULT_PUB : Public = Public::from_pub(Secp256k1::public_from_secret(&Secp256k1::zero_key()).expect("only one value"));
}

/// secret-store compatibility, does not make a lot of sense.
impl Default for Public {
	fn default() -> Public {
		DEFAULT_PUB.clone()
	}
}

impl DerefMut for Public {
	fn deref_mut (&mut self) -> &mut Self::Target {
		&mut self.inner
	}
}

impl PartialOrd<Public> for Public {
	fn partial_cmp(&self, other: &Public) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Public {
	// there is a more efficient implementation for fixed_hash
	fn cmp(&self, other: &Self) -> Ordering {
		self.inner.as_ref().cmp(other.inner.as_ref())
	}
}

impl DerefMut for Secret {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.inner
	}
}

impl Deref for Public {
	type Target = <Secp256k1 as Asym>::PublicKey;
	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl Deref for Secret {
	type Target = <Secp256k1 as Asym>::SecretKey;
	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl AsRef<[u8]> for Public {
	fn as_ref(&self) -> &[u8] {
		self.inner.as_ref()
	}
}

impl Into<H512> for Public {
	fn into(self) -> H512 {
		self.inner.as_ref().into()
	}
}

impl<'a> Into<H512> for &'a Public {
	fn into(self) -> H512 {
		self.inner.as_ref().into()
	}
}


impl AsRef<[u8]> for Secret {
	fn as_ref(&self) -> &[u8] {
		self.inner.as_ref()
	}
}

/* TODO 
impl From<<Secp256k1 as Asym>::PublicKey> for Public {
	fn from(inner: <Secp256k1 as Asym>::PublicKey) -> Self {
		Public { inner }
	}
}
*/
// TODO use from
//impl From<<Secp256k1 as Asym>::SecretKey> for Secret {
impl Secret {
	pub fn from_sec(inner: <Secp256k1 as Asym>::SecretKey) -> Self {
		Secret { inner }
	}
}

impl Public {
	pub fn from_pub(inner: <Secp256k1 as Asym>::PublicKey) -> Self {
		Public { inner }
	}

	pub fn from_slice(s: &[u8]) -> Result<Self, Error> {
		Ok(Public { inner: Secp256k1::public_from_slice(s)? })
	}
}

struct LHex<'a>(pub &'a[u8]);

impl<'a> std::fmt::LowerHex for LHex<'a> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		if f.alternate() {
			write!(f, "0x")?;
		}
		for i in &self.0[..] {
			write!(f, "{:02x}", i)?;
		}
		Ok(())
	}
}

impl ToHex for Secret {
	fn to_hex(&self) -> String {
		format!("{:x}", LHex(self.inner.as_ref()))
	}
}

impl ToHex for Public {
	fn to_hex(&self) -> String {
		format!("{:x}", LHex(self.inner.as_ref()))
	}
}

impl fmt::LowerHex for Secret {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		LHex(self.inner.as_ref()).fmt(fmt)
	}
}

impl fmt::LowerHex for Public {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		LHex(self.inner.as_ref()).fmt(fmt)
	}
}

impl fmt::Display for Secret {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		let v = self.inner.as_ref();
		write!(fmt, "Secret: 0x{:x}{:x}..{:x}{:x}", v[0], v[1], v[30], v[31])
	}
}

impl fmt::Display for Public {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		write!(fmt, "Public: {}", &self.to_hex())
	}
}


impl Secret {
	/// Creates a `Secret` from the given slice, returning `None` if the slice length != 32.
	pub fn from_slice(key: &[u8]) -> Option<Self> {
		if key.len() != 32 {
			return None
		}
		let v = Secp256k1::secret_from_slice(key).ok();
		v.map(|s|Secret::from_sec(s)) 
	}

	/// Creates zero key, which is invalid for crypto operations, but valid for math operation.
	pub fn zero() -> Self {
		Secret::from_sec(Secp256k1::zero_key().clone())
	}

	/// Imports and validates the key.
	pub fn from_unsafe_slice(key: &[u8]) -> Result<Self, Error> {
		let secret = Secp256k1::secret_from_slice(key)?;
		Ok(Secret::from_sec(secret))
	}

	/// Checks validity of this key.
	pub fn check_validity(&self) -> Result<(), Error> {
		self.to_secp256k1_secret().map(|_| ())
	}

	fn is_zero(&self) -> bool {
		&self.inner == Secp256k1::zero_key()
	}

	/// Inplace add one secret key to another (scalar + scalar)
	pub fn add(&mut self, other: &Secret) -> Result<(), Error> {
		match (self.is_zero(), other.is_zero()) {
			(true, true) | (false, true) => Ok(()),
			(true, false) => {
				*self = other.clone();
				Ok(())
			},
			(false, false) => {
				let mut key_secret = self.to_secp256k1_secret()?;
				let other_secret = other.to_secp256k1_secret()?;
				Secp256k1::secret_add(&mut key_secret, &other_secret)?;

				*self = Secret::from_sec(key_secret);
				Ok(())
			},
		}
	}

	/// Inplace subtract one secret key from another (scalar - scalar)
	pub fn sub(&mut self, other: &Secret) -> Result<(), Error> {
		match (self.is_zero(), other.is_zero()) {
			(true, true) | (false, true) => Ok(()),
			(true, false) => {
				*self = other.clone();
				self.neg()
			},
			(false, false) => {
				let mut key_secret = self.to_secp256k1_secret()?;
				let mut other_secret = other.to_secp256k1_secret()?;
				Secp256k1::secret_mul(&mut other_secret, Secp256k1::minus_one_key())?;
				Secp256k1::secret_add(&mut key_secret, &other_secret)?;

				*self = Secret::from_sec(key_secret);
				Ok(())
			},
		}
	}

	/// Inplace decrease secret key (scalar - 1)
	pub fn dec(&mut self) -> Result<(), Error> {
		match self.is_zero() {
			true => {
				let key_secret = Secp256k1::minus_one_key().clone();
				*self = Secret::from_sec(key_secret);
				Ok(())
			},
			false => {
				let mut key_secret = self.to_secp256k1_secret()?;
				Secp256k1::secret_add(&mut key_secret, Secp256k1::minus_one_key())?;

				*self = Secret::from_sec(key_secret);
				Ok(())
			},
		}
	}

	/// Inplace multiply one secret key to another (scalar * scalar)
	pub fn mul(&mut self, other: &Secret) -> Result<(), Error> {
		match (self.is_zero(), other.is_zero()) {
			(true, true) | (true, false) => Ok(()),
			(false, true) => {
				*self = Self::zero();
				Ok(())
			},
			(false, false) => {
				let mut key_secret = self.to_secp256k1_secret()?;
				let other_secret = other.to_secp256k1_secret()?;
				Secp256k1::secret_mul(&mut key_secret, &other_secret)?;

				*self = Secret::from_sec(key_secret);
				Ok(())
			},
		}
	}

	/// Inplace negate secret key (-scalar)
	pub fn neg(&mut self) -> Result<(), Error> {
		match self.is_zero() {
			true => Ok(()),
			false => {
				let mut key_secret = self.to_secp256k1_secret()?;
				Secp256k1::secret_mul(&mut key_secret, Secp256k1::minus_one_key())?;

				*self = Secret::from_sec(key_secret);
				Ok(())
			},
		}
	}

	/// Inplace inverse secret key (1 / scalar)
	pub fn inv(&mut self) -> Result<(), Error> {
		let mut key_secret = self.to_secp256k1_secret()?;
		Secp256k1::secret_inv(&mut key_secret)?;

		*self = Secret::from_sec(key_secret);
		Ok(())
	}

	/// Compute power of secret key inplace (secret ^ pow).
	/// This function is not intended to be used with large powers.
	pub fn pow(&mut self, pow: usize) -> Result<(), Error> {
		if self.is_zero() {
			return Ok(());
		}

		match pow {
			0 => *self = Secret::from_sec(Secp256k1::one_key().clone()),
			1 => (),
			_ => {
				let c = self.clone();
				for _ in 1..pow {
					self.mul(&c)?;
				}
			},
		}

		Ok(())
	}

	/// Create `secp256k1::SecretKey` based on this secret
	pub fn to_secp256k1_secret(&self) -> Result<<Secp256k1 as Asym>::SecretKey, Error> {
		Ok(self.inner.clone())
	}
}

impl FromStr for Secret {
	type Err = Error;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(H256::from_str(s).map_err(|e| Error::Custom(format!("{:?}", e)))?.into())
	}
}

impl FromStr for Public {
	type Err = Error;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(H512::from_str(s).map_err(|e| Error::Custom(format!("{:?}", e)))?.into())
	}
}


impl From<[u8; 32]> for Secret {
	fn from(k: [u8; 32]) -> Self {
		let s = Secp256k1::secret_from_slice(&k[..]).expect("right size");
		Secret::from_sec(s)
	}
}

impl From<H256> for Secret {
	fn from(s: H256) -> Self {
		s.0.into()
	}
}

impl From<&'static str> for Secret {
	fn from(s: &'static str) -> Self {
		s.parse().expect(&format!("invalid string literal for {}: '{}'", stringify!(Self), s))
	}
}

impl From<[u8; 64]> for Public {
	fn from(k: [u8; 64]) -> Self {
		let s = Secp256k1::public_from_slice(&k[..]).expect("right size");
		Public::from_pub(s)
	}
}

impl From<H512> for Public {
	fn from(s: H512) -> Self {
		s.0.into()
	}
}

impl From<&'static str> for Public {
	fn from(s: &'static str) -> Self {
		s.parse().expect(&format!("invalid string literal for {}: '{}'", stringify!(Self), s))
	}
}



#[cfg(test)]
mod tests {
	use std::str::FromStr;
	use super::super::{Random, Generator};
	use super::Secret;

	#[test]
	fn multiplicating_secret_inversion_with_secret_gives_one() {
		let secret = Random.generate().unwrap().secret().clone();
		let mut inversion = secret.clone();
		inversion.inv().unwrap();
		inversion.mul(&secret).unwrap();
		assert_eq!(inversion, Secret::from_str("0000000000000000000000000000000000000000000000000000000000000001").unwrap());
	}

	#[test]
	fn secret_inversion_is_reversible_with_inversion() {
		let secret = Random.generate().unwrap().secret().clone();
		let mut inversion = secret.clone();
		inversion.inv().unwrap();
		inversion.inv().unwrap();
		assert_eq!(inversion, secret);
	}

	#[test]
	fn secret_pow() {
		let secret = Random.generate().unwrap().secret().clone();

		let mut pow0 = secret.clone();
		pow0.pow(0).unwrap();
		assert_eq!(pow0, Secret::from_str("0000000000000000000000000000000000000000000000000000000000000001").unwrap());

		let mut pow1 = secret.clone();
		pow1.pow(1).unwrap();
		assert_eq!(pow1, secret);

		let mut pow2 = secret.clone();
		pow2.pow(2).unwrap();
		let mut pow2_expected = secret.clone();
		pow2_expected.mul(&secret).unwrap();
		assert_eq!(pow2, pow2_expected);

		let mut pow3 = secret.clone();
		pow3.pow(3).unwrap();
		let mut pow3_expected = secret.clone();
		pow3_expected.mul(&secret).unwrap();
		pow3_expected.mul(&secret).unwrap();
		assert_eq!(pow3, pow3_expected);
	}
}
