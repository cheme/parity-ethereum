// Copyright 2015-2019 Parity Technologies (UK) Ltd.
// This file is part of Parity Ethereum.

// Parity Ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Ethereum.  If not, see <http://www.gnu.org/licenses/>.

//! Façade crate for `patricia_trie` for Ethereum specific impls

pub extern crate patricia_trie as trie; // `pub` because we need to import this crate for the tests in `patricia_trie` and there were issues: https://gist.github.com/dvdplm/869251ee557a1b4bd53adc7c971979aa
extern crate elastic_array;
extern crate parity_bytes;
extern crate ethereum_types;
extern crate hashdb;
extern crate keccak_hasher;
extern crate rlp;
extern crate kvdb;
extern crate rkv;
extern crate kvdb_rocksdb as rocksdb;
extern crate memorydb;
mod rlp_node_codec;
use memorydb::MemoryDB;
use trie::{TrieMut, Trie, DBValue, node::Node, NibbleSlice, NodeCodec};
use hashdb::{HashDB, Hasher};
pub use rlp_node_codec::RlpNodeCodec;
use kvdb::KeyValueDB;
use ethereum_types::H256;
use keccak_hasher::KeccakHasher;
use rlp::DecoderError;

/// Convenience type alias to instantiate a Keccak-flavoured `RlpNodeCodec`
pub type RlpCodec = RlpNodeCodec<KeccakHasher>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `TrieDB`
///
/// Use it as a `Trie` trait object. You can use `db()` to get the backing database object.
/// Use `get` and `contains` to query values associated with keys in the trie.
///
/// # Example
/// ```
/// extern crate patricia_trie as trie;
/// extern crate patricia_trie_ethereum as ethtrie;
/// extern crate hashdb;
/// extern crate keccak_hasher;
/// extern crate memorydb;
/// extern crate ethereum_types;
/// extern crate elastic_array;
///
/// use trie::*;
/// use hashdb::*;
/// use keccak_hasher::KeccakHasher;
/// use memorydb::*;
/// use ethereum_types::H256;
/// use ethtrie::{TrieDB, TrieDBMut};
/// use elastic_array::ElasticArray128;
///
/// type DBValue = ElasticArray128<u8>;
///
/// fn main() {
///   let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
///   let mut root = H256::new();
///   TrieDBMut::new(&mut memdb, &mut root).insert(b"foo", b"bar").unwrap();
///   let t = TrieDB::new(&memdb, &root).unwrap();
///   assert!(t.contains(b"foo").unwrap());
///   assert_eq!(t.get(b"foo").unwrap().unwrap(), DBValue::from_slice(b"bar"));
/// }
/// ```
pub type TrieDB<'db> = trie::TrieDB<'db, KeccakHasher, RlpCodec>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `SecTrieDB`
pub type SecTrieDB<'db> = trie::SecTrieDB<'db, KeccakHasher, RlpCodec>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `FatDB`
pub type FatDB<'db> = trie::FatDB<'db, KeccakHasher, RlpCodec>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `TrieDBMut`
///
/// Use it as a `TrieMut` trait object. You can use `db()` to get the backing database object.
/// Note that changes are not committed to the database until `commit` is called.
/// Querying the root or dropping the trie will commit automatically.

/// # Example
/// ```
/// extern crate patricia_trie as trie;
/// extern crate patricia_trie_ethereum as ethtrie;
/// extern crate hashdb;
/// extern crate keccak_hash;
/// extern crate keccak_hasher;
/// extern crate memorydb;
/// extern crate ethereum_types;
/// extern crate elastic_array;
///
/// use keccak_hash::KECCAK_NULL_RLP;
/// use ethtrie::{TrieDBMut, trie::TrieMut};
/// use keccak_hasher::KeccakHasher;
/// use memorydb::*;
/// use ethereum_types::H256;
/// use elastic_array::ElasticArray128;
///
/// type DBValue = ElasticArray128<u8>;
///
/// fn main() {
///   let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
///   let mut root = H256::new();
///   let mut t = TrieDBMut::new(&mut memdb, &mut root);
///   assert!(t.is_empty());
///   assert_eq!(*t.root(), KECCAK_NULL_RLP);
///   t.insert(b"foo", b"bar").unwrap();
///   assert!(t.contains(b"foo").unwrap());
///   assert_eq!(t.get(b"foo").unwrap().unwrap(), DBValue::from_slice(b"bar"));
///   t.remove(b"foo").unwrap();
///   assert!(!t.contains(b"foo").unwrap());
/// }
/// ```
pub type TrieDBMut<'db> = trie::TrieDBMut<'db, KeccakHasher, RlpCodec>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `SecTrieDBMut`
pub type SecTrieDBMut<'db> = trie::SecTrieDBMut<'db, KeccakHasher, RlpCodec>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `FatDBMut`
pub type FatDBMut<'db> = trie::FatDBMut<'db, KeccakHasher, RlpCodec>;

/// Convenience type alias to instantiate a Keccak/Rlp-flavoured `TrieFactory`
pub type TrieFactory = trie::TrieFactory<KeccakHasher, RlpCodec>;

/// Convenience type alias for Keccak/Rlp flavoured trie errors
pub type TrieError = trie::TrieError<H256, DecoderError>;
/// Convenience type alias for Keccak/Rlp flavoured trie results
pub type Result<T> = trie::Result<T, H256, DecoderError>;


#[test]
fn experimenttest() {
  experiment()
}

/*#[test]
fn depth() {
let a: &[u8] = &[0, 11, 71, 140, 124, 136, 184, 231, 226, 44];
let b: &[u8] = &[0, 11, 224, 137, 13, 168, 7, 67, 202, 151];
assert_eq!(5, biggest_depth(&a[..],&b[..]));
}*/
// warn start at 1...
fn biggest_depth(v1: &[u8], v2: &[u8]) -> usize {
  for a in 0..v1.len() {
    if v1[a] == v2[a] {
    } else {
      if v1[a] >> 4 ==  v2[a] >> 4 {
        return a * 2 + 2;
      } else {
        return a * 2 + 1;
      }
    }
  }
  return 1;
}
fn flush_queue (ix: usize, 
               target_depth: usize, 
                val_queue: &[(Box<[u8]>,Box<[u8]>)], 
                memdb: &MemoryDB::<KeccakHasher, DBValue>,
                hashdb: &mut MemoryDB::<KeccakHasher, DBValue>,
                nbelt: usize,
                ) -> usize {
    for i in 0..ix+1 {
      let (ref k2,ref v2) = &val_queue[i]; 
          let mut found = false;
          let nkey = NibbleSlice::new_offset(&k2[..],target_depth).encoded(true);
          let encoded = RlpNodeCodec::leaf_node(&nkey[..], &v2[..]);
          let hash = hashdb.insert(&encoded[..]);
          if memdb.contains(&hash) {
            if nbelt < 30 {
              println!("found a leaf {}, depth {}",nbelt, target_depth);
              println!("k {:?}", &k2[..10]);
            }
          } else {
            panic!("not a leaf {}", nbelt);
          }

/*          for depth in 0..64 { // or 65 ??
            //let partial = NibbleSlice::new(&k2[..]);
            let nkey = NibbleSlice::new_offset(&k2[..],depth).encoded(true);
            //let ns = NibbleSlice::new_offset(&k2[..],32);
            // leaf situation
            //let leaf = Node::Leaf(ns, &v2[..]);
            let encoded = RlpNodeCodec::leaf_node(&nkey[..], &v2[..]);
            //let encoded = leaf.into_encoded(|node_handle| self.commit_child(node_handle) );
            let hash = hashdb.insert(&encoded[..]);
//						let encoded = leaf.into_encoded::<_, C, H>(|node_handle| self.commit_child(node_handle) );
            if memdb.contains(&hash) {
              //if nbelt < 30 {
              println!("found a leaf {}, depth {}, calcdepth {}",nbelt, depth, target_depth);
              println!("k {:?}", &k2[..10]);
              //}
              assert_eq!(depth, target_depth);
              found = true;
              break;
            } else {
          //    panic!("not a leaf {}", nbelt);
            }
          }
          if !found {
            panic!("not a leaf {}", nbelt);
          }*/
    }
 
    return ix+1;
  }

pub enum ParseState {
  Start,
  // ix then depth
  Depth(usize,usize),// no define depth and slice index of queue
}
// warn run on unmodified parity-common (branch is too hacky broken)
fn experiment() {
	let tempdirlmdb  = std::path::Path::new("./all2");
    let mut env = rkv::Rkv::environment_builder();
  env.set_map_size(10485760 * 2);
let created_arc = rkv::Manager::singleton().write().unwrap()
  .get_or_create(tempdirlmdb, |p|rkv::Rkv::from_env(p,env))
  .unwrap()
  ;
let env = created_arc.read().unwrap();

	let tempdir  = std::path::Path::new("orig");

let store: rkv::Store = env.open_or_create_default().unwrap();


	let config = rocksdb::DatabaseConfig::default();
	let mut db = rocksdb::Database::open(&config, tempdir.to_str().unwrap()).unwrap();
	let mut db: &mut dyn KeyValueDB = &mut db;
  
  let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut hashdb = MemoryDB::<KeccakHasher, DBValue>::new();

  let root = {
    let mut root = H256::new();
    let mut t = TrieDBMut::new(&mut memdb, &mut root);
    let mut nbelt = 0;
    let mut writerlm = env.write().unwrap();
    for (k, v) in db.iter(None) {
      nbelt += 1;
      t.insert(k[..].into(),v[..].into()).unwrap();
      writerlm.put(store.clone(), k[..].to_vec(), &rkv::Value::Blob(&v[..])).unwrap();
    }
    writerlm.commit().unwrap();
    t.root().clone()
  };

  let mut state = ParseState::Start;
  let nv: (Box<[u8]>,Box<[u8]>) = (Box::new([]),Box::new([]));
  let mut val_queue : Vec<(Box<[u8]>,Box<[u8]>)> = vec![nv.clone();16];
  // compare iter ordering
  {
    let t = TrieDB::new(&memdb, &root);
    let mut nbelt = 0;
    let mut nbflush = 0;
    let readerlm: rkv::Reader<Vec<u8>>  = env.read().unwrap();
    let mut iterlm = readerlm.iter_start(store.clone()).unwrap();
      for (k, v) in db.iter(None) {
      nbelt += 1;
      // TODO rkv api is not low level enough
      if let Some((k2,Ok(Some(rkv::Value::Blob(v2))))) = iterlm.next() {

        assert_eq!(&k[..],&k2[..]);
        assert_eq!(&v[..],&v2[..]);
        match state {
          ParseState::Start => {
            val_queue[0] = (k, v);
            state = ParseState::Depth(0,0);
          },
          ParseState::Depth(ix, depth) => {
            let common_depth = biggest_depth(&val_queue[ix].0[..], &k[..]);
            if common_depth == depth {
              val_queue[ix+1] = (k, v);
              state = ParseState::Depth(ix+1, common_depth);
            } else if common_depth > depth {
              if ix == 0 {
                // nothing
              } else {
                nbflush += flush_queue(ix - 1, depth, &val_queue[..], &memdb, &mut hashdb, nbelt);
                // TODO rusty clone : unsafe that??
                val_queue[0] = std::mem::replace(&mut val_queue[ix],nv.clone());
              }
              val_queue[1] = (k, v);
              state = ParseState::Depth(1, common_depth);
            } else if common_depth < depth {
              nbflush += flush_queue(ix, depth, &val_queue[..], &memdb, &mut hashdb, nbelt);
              val_queue[0] = (k, v);
              state = ParseState::Depth(0, common_depth);
            }
          }
        }
//        panic!("{:?}, {:?}\n{:?}, {:?}", k, v, k2, v2);
      } else {
        panic!("{:?}, {:?}", k, v);
      }

    }
    // pending
    match state {
      ParseState::Start => {
        // nothing null root case
      },
      ParseState::Depth(ix, depth) => {
        nbflush += flush_queue(ix, depth, &val_queue[..], &memdb, &mut hashdb, nbelt);
      }
    }

    assert!(iterlm.next().is_none());
    assert!(memdb.contains(&root));
    panic!("ok eq: {:?}, {}, nbfl {}", nbelt, memdb.keys().len(), nbflush);
 
  }
	/*for &(ref key, ref value) in &x {
		assert!(t.insert(key, value).unwrap().is_none());
		assert_eq!(t.insert(key, value).unwrap(), Some(DBValue::from_slice(value)));
	}

	for (key, value) in x {
		assert_eq!(t.remove(&key).unwrap(), Some(DBValue::from_slice(&value)));
		assert!(t.remove(&key).unwrap().is_none());
	}*/

}

