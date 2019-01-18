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
// TODO some variant with context could probably optimize that
// (but for now keep the slow version)
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

// warn! start at 0 // TODO change biggest_depth??
// warn! slow don't loop on that
fn nibble_at(v1: &[u8], ix: usize) -> u8 {
  if ix % 2 == 0 {
    v1[ix/2] >> 4
  } else {
    v1[ix/2] & 15
  }
}

fn flush_branch (
  ref_branch: Box<[u8]>,
  new_depth: usize, 
  old_depth: usize, 
  memdb: &MemoryDB::<KeccakHasher, DBValue>,
  hashdb: &mut MemoryDB::<KeccakHasher, DBValue>,
  nbelt: usize,
  depth_queue : &mut Vec<Vec<H256>>, //(64 * 16 size) 
) -> usize {
      if nbelt < 20 {
println!("t{}-{}", old_depth, new_depth);
      }
//      let new_depth = new_depth -1;
//      let old_depth = old_depth -1;
  let mut ret = 0;
  // -1 ix
  for d in (new_depth..old_depth).rev() {
      if nbelt < 5 {
println!("ti{}", d);
      }
 
    // check if branch empty TODO switch to optional storage
    let mut empty = true;
    let mut unit: usize = 16;
    for i in 0..16 {
      if &H256::new()[..]!= &depth_queue[d][i][..] {
        empty = false;
        if unit > 15 {
          unit = i;
        } else {
          unit = 16;
          break;
        }
      }
    }

/*    if empty {
      // check extension cache
      if unimplemented!() {

      }
    }*/
    if unit < 16 {
      /*// TODO check extension cache to invalidate unit
      if unimplemented!() {
        // TODO fill extension cache!! + nibble
        unit = 16;
      } else {
        // TODO extension it
        
      }*/
      // one length extension testing TODO stack it in cache and stack its nibbles

      if d > 0 {
//        let nibble: u8 = nibble_at(&ref_branch[..],d-1);
 //       let nibl = NibbleSlice::new_offset(&ref_branch[..], d);
 //           let partial = nibl.encoded_leftmost(d-dp, false);
            let v_hash: H256 = depth_queue[d][unit].clone();
            let v_hashd = v_hash.clone();
            depth_queue[d][unit] = H256::new(); // TODO use mem replace avoid copy
            // TODO extension
            let encoded = RlpNodeCodec::ext_node(&[16 + unit as u8], trie::ChildReference::Hash(v_hash));
            let hash = hashdb.insert(&encoded[..]);
            let valid =  memdb.contains(&hash);
            if valid {
              // put to parent (TODO put to cache)
              let nibble: u8 = nibble_at(&ref_branch[..],d-1);
              depth_queue[d-1][nibble as usize] = hash;
            } else {
            /*  let v = memdb.get(&v_hashd).unwrap();

      let dec : Node = RlpNodeCodec::decode(&v[..]).unwrap();
      println!("{:?}", dec);
              panic!("{}: {:?}, {}", unit, v_hashd, d);*/
            }
       
      }
    }
    if !empty && unit > 15 {
    	//fn branch_node<I>(children: Iterator<H256>, value: Option<ElasticArray128<u8>>) -> Vec<u8>
      // TODO encode on buffer struct (do not stick to existing one)
      let encoded = RlpNodeCodec::branch_node(depth_queue[d].iter().map(|v| if v == &H256::new() { None } else {Some(trie::ChildReference::Hash(v.clone()))}), None);
      depth_queue[d] = vec![H256::new();16];
      /*let dec : Node = RlpNodeCodec::decode(&encoded[..]).unwrap();
      println!("{:?}", dec);
      panic!("d");*/
      let hash = hashdb.insert(&encoded[..]);
      let valid =  memdb.contains(&hash);
      // clear tmp val
      // put hash in parent
      if d > 0 {
      let nibble: u8 = nibble_at(&ref_branch[..],d-1);
      depth_queue[d-1][nibble as usize] = hash;
      } else {
        println!("TODO root");
      }
 /* 
      // update not empty parent -> wrong approach : cannnot manage ext like that
      for dp in (0..d).rev() {
        let mut empty = true;
        for i in 0..16 {
          if &H256::new()[..] != &depth_queue[dp][i][..] {
            empty = false;
            break;
          }
        }
        if dp == 0 || !empty {
//        if !empty {
          if d - dp == 1 {
            let nibble: u8 = nibble_at(&ref_branch[..],dp);
            depth_queue[dp][nibble as usize] = hash;
          } else {
            let hashd = hash.clone();
            let nibl = NibbleSlice::new_offset(&ref_branch[..], d);
            let partial = nibl.encoded_leftmost(d-dp, false);
            // TODO extension
            let encoded = RlpNodeCodec::ext_node(&partial[..], trie::ChildReference::Hash(hash));
            let hash = hashdb.insert(&encoded[..]);
            let valid =  memdb.contains(&hash);
            if valid {
              println!("valid ext");
            } else {
              panic!("{:x?}: {:?}, {}, {}, {:x?}", partial, hashd, d,dp, &ref_branch[..]);
            }
          }
          break;
        }
      }
*/


//      if nbelt < 20 {
      if valid {
      // 2.76k validterminals
      // build branch
//      println!("Non empty br {}, valid {:?}", d+1, valid);
      } else {
      // 730 aka contains other branches
      // 119 aka contains extension
      // 21 aka need extension of size > 1
              ret += 1;
        // nothing
      }
    }
  }
  ret
}
 
fn flush_queue (ix: usize, 
               target_depth: usize, 
                val_queue: &[(Box<[u8]>,Box<[u8]>)], 
                memdb: &MemoryDB::<KeccakHasher, DBValue>,
                hashdb: &mut MemoryDB::<KeccakHasher, DBValue>,
                nbelt: usize,
                depth_queue : &mut Vec<Vec<H256>>, //(64 * 16 size) 
                ) -> usize {
    for i in 0..ix+1 {
      let (ref k2,ref v2) = &val_queue[i]; 
          let mut found = false;
          // TODO For branch value the nibble at will probably fail: then just update parent branch
          // (easy?)
          let nibble_value = nibble_at(&k2[..], target_depth-1);
          let k3 = H256::from(&k2[..]);
          let nkey = NibbleSlice::new_offset(&k2[..],target_depth).encoded(true);
          // Note: fwiu, having fixed key size, all values are in leaf (no value in
          // branch). TODO run metrics on a node to count branch with values
          let encoded = RlpNodeCodec::leaf_node(&nkey[..], &v2[..]);
          let hash = hashdb.insert(&encoded[..]);
          // insert hash in branch (first level branch only at this point)
// for debugging posistion          depth_queue[target_depth - 1][nibble_value as usize] = k3;
          depth_queue[target_depth - 1][nibble_value as usize] = hash.clone();

          if memdb.contains(&hash) {
            if nbelt < 20 {
              println!("found a leaf {}, depth {}",nbelt, target_depth);
              println!("k {:x?}", &k2[..10]);
              //println!("br {:?}", depth_queue[target_depth - 1]);
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
/*  {
    let mut t = TrieDB::new(&memdb, &root);
    println!("{:#?}", t);
  }*/
  let mut state = ParseState::Start;
  let nv: (Box<[u8]>,Box<[u8]>) = (Box::new([]),Box::new([]));
  // TODO here nibble size at 4bit. TODO probably possibility or more than 16 (aka depth * 16 but
  // less because it needs some filling TODO recheck algo
  let mut val_queue : Vec<(Box<[u8]>,Box<[u8]>)> = vec![nv.clone();16];
  // TODO here static max depth for 256 fixed size = 64. TODO maybe 63 ??
  // store branch in construction: one per level I think
  // TODO inefficient mem whise (64*16*32): could use empty matrix or box<rc>
  // TODO layout of Vec<Vec< sucks. -> go full static with [] for empty h256 would be ideal
  // (no H256 use and cal hash with custo fn (need hash function filling a mutable buffer(which
  // contradicts [] -> need to box I guess).
  let mut depth_queue : Vec<Vec<H256>> = vec![vec![H256::new();16];64];
  // compare iter ordering
  {
    let t = TrieDB::new(&memdb, &root);
    let mut nbelt = 0;
    let mut nbflush = 0;
    let mut nbbranch = 0;
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
                nbflush += flush_queue(ix - 1, depth, &val_queue[..], &memdb, &mut hashdb, nbelt, &mut depth_queue);
                // TODO rusty clone : unsafe that??
                val_queue[0] = std::mem::replace(&mut val_queue[ix],nv.clone());
              }
              val_queue[1] = (k, v);
              state = ParseState::Depth(1, common_depth);
            } else if common_depth < depth {
              let ref_branches = val_queue[ix].0.clone(); // TODO this clone should be avoid by returning from flush_queue
              nbflush += flush_queue(ix, depth, &val_queue[..], &memdb, &mut hashdb, nbelt, &mut depth_queue);
              nbbranch += flush_branch(ref_branches, common_depth, depth, &memdb, &mut hashdb, nbflush, &mut depth_queue);
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
        let ref_branches = val_queue[ix].0.clone(); // TODO this clone should be avoid by returning from flush_queue
        nbflush += flush_queue(ix, depth, &val_queue[..], &memdb, &mut hashdb, nbelt, &mut depth_queue);
        // TODO shouldn't it be 1 instead of 0??
        nbbranch += flush_branch(ref_branches, 0, depth, &memdb, &mut hashdb, nbflush, &mut depth_queue);
      }
    }

    assert!(iterlm.next().is_none());
    assert!(memdb.contains(&root));
    panic!("ok eq: {:?}, {}, nbfl {}, nbbr {}", nbelt, memdb.keys().len(), nbflush, nbbranch);
 
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

