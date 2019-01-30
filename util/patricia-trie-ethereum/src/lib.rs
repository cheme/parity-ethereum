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
use elastic_array::ElasticArray36;
use std::marker::PhantomData;

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
// TODO remove for nibbleslice api TODO can be variable size
fn encoded_nibble(ori: &[u8], is_leaf: bool) -> ElasticArray36<u8> {
	let l = ori.len();
	let mut r = ElasticArray36::new();
	let mut i = l % 2;
	r.push(if i == 1 {0x10 + ori[0]} else {0} + if is_leaf {0x20} else {0});
	while i < l {
		r.push(ori[i] * 16 + ori[i+1]);
		i += 2;
	}
	r
}


// (64 * 16) aka 2*byte size of key * nb nibble value, 2 being byte/nible (8/4)
// TODO test others layout
// first usize to get nb of added value, second usize last added index
struct CacheAccum<H: Hasher,C> (Vec<(Vec<CacheNode<<H as Hasher>::Out>>, usize, usize)>,PhantomData<(H,C)>);

const DEPTH: usize = 64;
const NIBBLE_SIZE: usize = 16;
impl<H,C> CacheAccum<H,C>
where
  H: Hasher,
  C: NodeCodec<H>,
{
  // TODO switch to static and bench
  fn new() -> Self {
    CacheAccum(vec![(vec![CacheNode::None; NIBBLE_SIZE],0,0); DEPTH], PhantomData)
  }
  fn get_node(&self, depth:usize, nibble_ix:usize) -> &CacheNode<H::Out> {
    &self.0[depth].0[nibble_ix]
  }
  fn set_node(&mut self, depth:usize, nibble_ix:usize, node: CacheNode<H::Out>) {
    self.0[depth].0[nibble_ix] = node;
    // strong heuristic from the fact that we do not delete depth except globally
    // and that we only check relevant size for 0 and 1 TODO replace counter by enum
    // -> so we do not manage replace case
    self.0[depth].1 += 1;
    self.0[depth].2 = nibble_ix; // TODO bench a set if self.0[depth].1 is 0 (probably slower)
  }
  fn depth_added(&self, depth:usize) -> usize {
    self.0[depth].1
  }
  fn depth_last_added(&self, depth:usize) -> usize {
    self.0[depth].2
  }

  fn rem_node(&mut self, depth:usize, nibble:usize) -> CacheNode<H::Out> {
    self.0[depth].1 -= 1;
    self.0[depth].2 = NIBBLE_SIZE; // out of ix -> need to check all value in this case TODO optim it ??
    std::mem::replace(&mut self.0[depth].0[nibble], CacheNode::None)
  }
  fn reset_depth(&mut self, depth:usize) {
    self.0[depth] = (vec![CacheNode::None; NIBBLE_SIZE], 0, 0);
  }

  fn encode_branch_2(&self, depth:usize, cb_ext: &mut impl FnMut(Vec<u8>, bool) -> H::Out) -> Vec<u8>  {
    C::branch_node(
      self.0[depth].0.iter().map(|v| 
        match v {
          CacheNode::None => None,
          CacheNode::Hash(ref h) => Some(trie::ChildReference::Hash(h.clone())), // TODO try rem clone
          CacheNode::Ext(ref n, ref h) => {
            let mut n = n.to_vec();
            n.reverse();// TODO use proper encoded_nibble algo.
            let enc_nibble = encoded_nibble(&n[..], false);
            let encoded = C::ext_node(&enc_nibble[..], trie::ChildReference::Hash(h.clone())); // TODO try rem clone
            let h = cb_ext(encoded, false);
            Some(trie::ChildReference::Hash(h))
          },
        }
      ), None)
  }

 fn flush_queue_2<A,B> (
                &mut self, //(64 * 16 size) 
  cb_ext: &mut impl FnMut(Vec<u8>, bool) -> H::Out,
   ix: usize, 
               target_depth: usize, 
                val_queue: &[(A,B)], 
                nbelt: usize,
                ) -> usize 
where
	A: AsRef<[u8]> + Ord + Default + Clone,
	B: AsRef<[u8]> + Default + Clone,
{
    for i in 0..ix+1 {
      let (ref k2,ref v2) = &val_queue[i]; 
          let mut found = false;
          // TODO For branch value the nibble at will probably fail: then just update parent branch
          // (easy?)
          let nibble_value = nibble_at(&k2.as_ref()[..], target_depth-1);
          //let k3 = H256::from(&k2.as_ref()[..]);
          let nkey = NibbleSlice::new_offset(&k2.as_ref()[..],target_depth).encoded(true);
          // Note: fwiu, having fixed key size, all values are in leaf (no value in
          // branch). TODO run metrics on a node to count branch with values
          let encoded = RlpNodeCodec::leaf_node(&nkey.as_ref()[..], &v2.as_ref()[..]);
          let hash = cb_ext(encoded, false);
          // insert hash in branch (first level branch only at this point)
// for debugging posistion          depth_queue[target_depth - 1][nibble_value as usize] = k3;
          self.set_node(target_depth - 1, nibble_value as usize, CacheNode::Hash(hash.clone()));

            if nbelt < 20 {
              println!("found a leaf {}, depth {}",nbelt, target_depth);
              println!("k {:x?}", &k2.as_ref()[..10]);
              //println!("br {:?}", depth_queue[target_depth - 1]);
            }

    }
 
    return ix+1;
  }



fn flush_branch_2<A>(
  &mut self,
  cb_ext: &mut impl FnMut(Vec<u8>, bool) -> H::Out,
  ref_branch: A,
  new_depth: usize, 
  old_depth: usize, 
  nbelt: usize,
) -> usize 
where
	A: AsRef<[u8]> + Ord + Default + Clone,
{
      if nbelt < 20 {
println!("t{}-{}", old_depth, new_depth);
      }
  let mut ret = 0;
  for d in (new_depth..old_depth).rev() {
      if nbelt < 5 {
println!("ti{}", d);
      }
 
    // check if branch empty TODO switch to optional storage
    let mut empty = true;
    let depth_size = self.depth_added(d);
    if depth_size == 1 {
      let unit = self.depth_last_added(d);

      if d > 0 {
        let node = self.rem_node(d, unit);
        let nibble: u8 = nibble_at(&ref_branch.as_ref()[..],d-1);
        if let CacheNode::Ext(mut n,v_hash) = node {
          n.push(unit as u8);
          self.set_node(d-1, nibble as usize, CacheNode::Ext(n, v_hash));
        } else {
          let v_hash = node.hash();
          // TODO capacity vec of 64?
          self.set_node(d-1, nibble as usize, CacheNode::Ext(vec![unit as u8], v_hash));
        }
      } else {
        // TODO case test single element trie
      }
    }
    if depth_size > 1 {
    	//fn branch_node<I>(children: Iterator<H256>, value: Option<ElasticArray128<u8>>) -> Vec<u8>
      // TODO encode on buffer struct (do not stick to existing one)
      let encoded = self.encode_branch_2(d, cb_ext);
        
      self.reset_depth(d);
      /*let dec : Node = RlpNodeCodec::decode(&encoded[..]).unwrap();
      println!("{:?}", dec);
      panic!("d");*/
      let hash = cb_ext(encoded, d == 0);
      // clear tmp val
      // put hash in parent
      if d > 0 {
        let nibble: u8 = nibble_at(&ref_branch.as_ref()[..],d-1);
        self.set_node(d-1, nibble as usize, CacheNode::Hash(hash));
      } else {
        //println!("TODO root: {:x?}", &hash);
      }
      ret += 1;
    }
  }
  ret
}


}

// TODO try split struct
#[derive(Clone)]
enum CacheNode<HO> {
  None,
  Hash(HO),
  Ext(Vec<u8>,HO),// vec<u8> for nibble slice is not super good looking): TODO bench diff if explicitely boxed
}

impl<HO> CacheNode<HO>
where
  HO: Clone,
{
  // unsafe accessors TODO bench diff with safe one
  fn hash(self) -> HO {
    if let CacheNode::Hash(h) = self {
      return h
    }
    unreachable!()
  }
  fn ext(self) -> (Vec<u8>,HO) {
    if let CacheNode::Ext(n,h) = self {
      return (n,h)
    }
    unreachable!()
  }
}

pub enum ParseState {
  Start,
  // ix then depth
  Depth(usize,usize),// no define depth and slice index of queue
}

pub fn trie_visit<H, C, I, A, B, F>(input: I, cb_ext: &mut F) where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord + Default + Clone,
	B: AsRef<[u8]> + Default + Clone,
	H: Hasher,
  C: NodeCodec<H>,
  F: FnMut(Vec<u8>, bool) -> H::Out
{
//  let mut hashdb = MemoryDB::<KeccakHasher, DBValue>::new(); // TODO rem or put it in closure (only use to hash stuff)
  let mut state = ParseState::Start;
  let nv: (A,B) = Default::default();
  // TODO here nibble size at 4bit. TODO probably possibility or more than 16 (aka depth * 16 but
  // less because it needs some filling TODO recheck algo
  //let mut val_queue : Vec<(Box<[u8]>,Box<[u8]>)> = vec![nv.clone();NIBBLE_SIZE];
  let mut val_queue : Vec<(A,B)> = vec![nv.clone();NIBBLE_SIZE];
  // TODO here static max depth for 256 fixed size = 64. TODO maybe 63 ??
  // store branch in construction: one per level I think
  // TODO inefficient mem whise (64*16*32): could use empty matrix or box<rc>
  // TODO layout of Vec<Vec< sucks. -> go full static with [] for empty h256 would be ideal
  // (no H256 use and cal hash with custo fn (need hash function filling a mutable buffer(which
  // contradicts [] -> need to box I guess).
  let mut depth_queue = CacheAccum::<H,C>::new();
  // compare iter ordering
  {
    let mut nbelt = 0;
    let mut nbflush = 0;
    let mut nbbranch = 0;
      for (k, v) in input.into_iter() {
      nbelt += 1;

        match state {
          ParseState::Start => {
            val_queue[0] = (k, v);
            state = ParseState::Depth(0,0);
          },
          ParseState::Depth(ix, depth) => {
            let common_depth = biggest_depth(&val_queue[ix].0.as_ref()[..], &k.as_ref()[..]);
            if common_depth == depth {
              val_queue[ix+1] = (k, v);
              state = ParseState::Depth(ix+1, common_depth);
            } else if common_depth > depth {
              if ix == 0 {
                // nothing
              } else {
                nbflush += depth_queue.flush_queue_2(cb_ext, ix - 1, depth, &val_queue[..], nbelt);
                // TODO rusty clone : unsafe that??
                val_queue[0] = std::mem::replace(&mut val_queue[ix],nv.clone());
              }
              val_queue[1] = (k, v);
              state = ParseState::Depth(1, common_depth);
            } else if common_depth < depth {
              let ref_branches = val_queue[ix].0.clone(); // TODO this clone should be avoid by returning from flush_queue
              nbflush += depth_queue.flush_queue_2(cb_ext, ix, depth, &val_queue[..], nbelt);
              nbbranch += depth_queue.flush_branch_2(cb_ext, ref_branches, common_depth, depth, nbflush);
              val_queue[0] = (k, v);
              state = ParseState::Depth(0, common_depth);
            }
          }
        }

    }
    // pending
    match state {
      ParseState::Start => {
        // nothing null root case
        cb_ext(C::empty_node(), true);
      },
      ParseState::Depth(ix, depth) => {
        let ref_branches = val_queue[ix].0.clone(); // TODO this clone should be avoid by returning from flush_queue
        nbflush += depth_queue.flush_queue_2(cb_ext, ix, depth, &val_queue[..], nbelt);
        // TODO shouldn't it be 1 instead of 0??
        nbbranch += depth_queue.flush_branch_2(cb_ext, ref_branches, 0, depth, nbflush);
      }
    }

  }
}

#[test]
fn trie_full_block () {

	let tempdirlmdb  = std::path::Path::new("./all2");
  let mut env = rkv::Rkv::environment_builder();
  env.set_map_size(10485760 * 2);
  let created_arc = rkv::Manager::singleton().write().unwrap()
    .get_or_create(tempdirlmdb, |p|rkv::Rkv::from_env(p,env))
    .unwrap();
  let env = created_arc.read().unwrap();

  let store: rkv::Store = env.open_or_create_default().unwrap();


  let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut hashdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut root_new = H256::new();



	let tempdir  = std::path::Path::new("orig");
	let config = rocksdb::DatabaseConfig::default();
	let mut db = rocksdb::Database::open(&config, tempdir.to_str().unwrap()).unwrap();
	let mut db: &mut dyn KeyValueDB = &mut db;
  
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

  {
    let mut cb = |enc_ext: Vec<u8>, is_root: bool| {
        let hash = hashdb.insert(&enc_ext[..]);
        if is_root {
          root_new = hash.clone();
        };
        hash
    };
    let readerlm: rkv::Reader<Vec<u8>>  = env.read().unwrap();
    let mut iterlm = readerlm.iter_start(store.clone()).unwrap().map(|v|
      if let (k2,Ok(Some(rkv::Value::Blob(v2)))) = v {
        (k2, v2)
      } else {
        panic!("nothing else in this lmdb");
      }
    );
    trie_visit::<KeccakHasher, RlpCodec, _, _, _, _>(iterlm, &mut cb);
  }

  assert!(root == root_new);
  let empty = MemoryDB::<KeccakHasher, DBValue>::new();
  assert!(memdb != empty);
}

#[test]
fn trie_root_empty () {
  let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut hashdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut root_new = H256::new();
  {
    let mut cb = |enc_ext: Vec<u8>, is_root: bool| {
      let hash = hashdb.insert(&enc_ext[..]);
      if is_root {
        root_new = hash.clone();
      };
      hash
    };
    let data: Vec<(Vec<u8>,Vec<u8>)> = vec![];
    trie_visit::<KeccakHasher, RlpCodec, _, _, _, _>(data.into_iter(), &mut cb);
  }
  let root = {
    let mut root = H256::new();
    let mut t = TrieDBMut::new(&mut memdb, &mut root);
    let mut nbelt = 0;
    t.root().clone()
  };
  assert_eq!(root, root_new);

}
