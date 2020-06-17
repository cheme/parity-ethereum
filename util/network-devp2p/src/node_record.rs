use log::*;
use parity_crypto::publickey::Secret;
use std::path::PathBuf;
use std::pin::Pin;
use crate::{persistence::{save, load, DiskEntity}, node_table::NodeEndpoint};

pub type Enr = enr::Enr<secp256k1::SecretKey>;

const ENR_VERSION: &str = "v4";

pub struct EnrManager {
	secret: Pin<Box<secp256k1::SecretKey>>,
	inner: Enr,
	path: Option<PathBuf>,
}

impl EnrManager {
	fn save(&mut self) {
		if let Some(path) = &self.path {
			save(path, &self.inner);
		}
	}

	pub fn new(path: Option<PathBuf>, key: Secret, seq: u64) -> Option<Self> {
		let secret = Pin::new(Box::new(key.to_secp256k1_secret().ok()?));
		let mut b = enr::EnrBuilder::new(ENR_VERSION);
		b.seq(seq);
		let inner = b.build(&*secret).ok()?;
		let mut this = Self { secret, inner, path };
		this.save();
		Some(this)
	}

	pub fn load<P>(path: P, key: Secret) -> Option<Self>
	where
		PathBuf: From<P>
	{
		let path = PathBuf::from(path);
		let inner = load::<Enr>(&path)?;
		let secret = Pin::new(Box::new(key.to_secp256k1_secret().ok()?));
		let public = secp256k1::PublicKey::from_secret_key(&secp256k1::Secp256k1::new(), &secret);

		if inner.public_key() != public {
			warn!("ENR does not match the provided key");
			return None;
		}
		Some(Self { secret, inner, path: Some(path) })
	}

	#[cfg(test)]
	pub fn with_node_endpoint(mut self, endpoint: &NodeEndpoint) -> Self {
		self.set_node_endpoint(endpoint);
		self
	}

	pub fn set_node_endpoint(&mut self, endpoint: &NodeEndpoint) {
		const ENR_PROOF: &str = "Not enough data to go over the limit; qed";

		let seq = self.inner.seq();
		self.inner.set_tcp_socket(endpoint.address, &self.secret).expect(ENR_PROOF);
		self.inner.set_udp(endpoint.udp_port, &self.secret).expect(ENR_PROOF);
		// We just wrap here, unlikely to be a problem in our lifetimes unless the user sets seq high enough on purpose.
		self.inner.set_seq(seq.wrapping_add(1), &self.secret).expect(ENR_PROOF);
		self.save();
	}

	pub fn as_enr(&self) -> &Enr {
		&self.inner
	}

	#[cfg(test)]
	pub fn into_enr(self) -> Enr {
		self.inner.clone()
	}
}

impl DiskEntity for Enr {
	const FILENAME: &'static str = "enr";
	const DESCRIPTION: &'static str = "Ethereum Node Record";

	fn to_repr(&self) -> String {
		self.to_base64()
	}

	fn from_repr(s: &str) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
		Ok(s.parse()?)
	}
}

impl Drop for EnrManager {
	fn drop(&mut self) {
		use zeroize::Zeroize;
		let secret_key: &[u8] = &self.secret[..];
		// unsafe cast since IndexMut is not implemented
		unsafe {
			#[allow(mutable_transmutes)]
			let secret_key_mut: &mut[u8] = std::mem::transmute(secret_key);
			secret_key_mut.zeroize();
		}
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn save_load() {
		use super::*;
		use ethereum_types::H256;
		use std::net::SocketAddr;
		use tempfile::TempDir;

		let tempdir = TempDir::new().unwrap();
		let key = Secret::from(H256::random());

		let mut enr = EnrManager::new(Some(tempdir.path().into()), key.clone(), 0).unwrap();
		assert_eq!(*enr.as_enr(), EnrManager::load(tempdir.path(), key.clone()).unwrap().into_enr());
		let endpoint = NodeEndpoint {
			address: SocketAddr::from((rand::random::<[u8; 4]>(), rand::random())),
			udp_port: rand::random(),
		};
		enr.set_node_endpoint(&endpoint);
		assert_eq!(*enr.as_enr(), EnrManager::load(tempdir.path(), key).unwrap().into_enr());
	}
}
