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
use trie::{TrieMut, Trie, DBValue, node::Node, NibbleSlice, NodeCodec, ChildReference};
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
/*#[test]
fn depth() {
let a: &[u8] = &[1,2,3,3];
let b: &[u8] = &[1,2,3,4];
assert_eq!(8, biggest_depth(&a[..],&b[..]));
}*/

// warn start at 1... AKA first differ depth (aka the branch ix starting at 1) -> TODO change that!!!
// TODO some variant with context could probably optimize that
// (but for now keep the slow version)
// Index of potential branch is the
// biggest common depth (indexing starting at 0).
fn biggest_depth(v1: &[u8], v2: &[u8]) -> usize {
  //for a in 0.. v1.len(), v2.len()) { sorted assertion preventing out of bound TODO fuzz that
  for a in 0.. v1.len() {
    if v1[a] == v2[a] {
    } else {
      if (v1[a] >> 4) ==  (v2[a] >> 4) {
        return a * 2 + 1;
      } else {
        println!("{} {}", v1[a], v2[a]);
        println!("{} {}", v1[a] >> 4, v2[a] >> 4);
        return a * 2;
      }
    }
  }
  return v1.len() * 2;
}

// warn! start at 0 // TODO change biggest_depth??
// warn! slow don't loop on that when possible
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
// second str is in branch value and can be remove for fix key scenario
struct CacheAccum<H: Hasher,C,V> (Vec<(Vec<CacheNode<<H as Hasher>::Out>>, usize, usize)>,Vec<Option<V>>,PhantomData<(H,C)>);

const DEPTH: usize = 64;
const NIBBLE_SIZE: usize = 16;
impl<H,C,V> CacheAccum<H,C,V>
where
  H: Hasher,
  C: NodeCodec<H>,
  V: AsRef<[u8]>,
  {
  // TODO switch to static and bench
  fn new() -> Self {
    CacheAccum(vec![(vec![CacheNode::None; NIBBLE_SIZE],0,0); DEPTH],
    std::iter::repeat_with(|| None).take(DEPTH).collect() // vec![None; DEPTH] for non clone
    , PhantomData)
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

  fn encode_branch(&mut self, depth:usize, has_val: bool, cb_ext: &mut impl FnMut(Vec<u8>, bool) -> ChildReference<H::Out>) -> Vec<u8>  {
    C::branch_node(
      self.0[depth].0.iter().map(|v| 
        match v {
          CacheNode::Hash(ref h) => Some(clone_child_ref(h)), // TODO try to avoid that clone
          CacheNode::Ext(ref n, ref h) => {
            let mut n = n.to_vec();
            n.reverse();// TODO use proper encoded_nibble algo.
            let enc_nibble = encoded_nibble(&n[..], false); // not leaf!!
            let encoded = C::ext_node(&enc_nibble[..], clone_child_ref(h));
            let h = cb_ext(encoded, false);
            Some(h)
          },
          CacheNode::None => None,
        }
      ), if has_val {
        std::mem::replace(&mut self.1[depth], None).map(|v|v.as_ref().into()) // TODO value could be a &[u8] instead of elastic!!
      } else { None })
  }

  fn flush_val (
    &mut self, //(64 * 16 size) 
    cb_ext: &mut impl FnMut(Vec<u8>, bool) -> ChildReference<H::Out>,
    target_depth: usize, 
    &(ref k2, ref v2): &(impl AsRef<[u8]>,impl AsRef<[u8]>), 
  ) {
    let nibble_value = nibble_at(&k2.as_ref()[..], target_depth-1);
    // is it a branch value (two candidate same ix)
    let nkey = NibbleSlice::new_offset(&k2.as_ref()[..],target_depth).encoded(true);
    // Note: fwiu, having fixed key size, all values are in leaf (no value in
    // branch). TODO run metrics on a node to count branch with values
    let encoded = C::leaf_node(&nkey.as_ref()[..], &v2.as_ref()[..]);
    let hash = cb_ext(encoded, false);
    // insert hash in branch (first level branch only at this point)
    // for debugging posistion          depth_queue[target_depth - 1][nibble_value as usize] = k3;
    self.set_node(target_depth - 1, nibble_value as usize, CacheNode::Hash(hash));
  }

  fn flush_branch(
    &mut self,
    cb_ext: &mut impl FnMut(Vec<u8>, bool) -> ChildReference<H::Out>,
    ref_branch: impl AsRef<[u8]> + Ord,
    new_depth: usize, 
    old_depth: usize, 
  ) {
    for d in (new_depth..old_depth).rev() {
   
      // check if branch empty TODO switch to optional storage
      let mut empty = true;
      let has_val = self.1[d].is_some();
      let depth_size = self.depth_added(d);
      assert!(depth_size != 0);
      if !has_val && depth_size == 1 {
        // extension case
        let unit = self.depth_last_added(d);

        let node = self.rem_node(d, unit);
        // already extension
        if let CacheNode::Ext(mut n,v_hash) = node {
          if d > 0 {
            let nibble: u8 = nibble_at(&ref_branch.as_ref()[..],d-1);
            n.push(unit as u8);
            self.set_node(d-1, nibble as usize, CacheNode::Ext(n, v_hash));
          } else {
            n.push(unit as u8);
            n.reverse(); // TODO use proper encoded_nibble algo.
            let enc_nibble = encoded_nibble(&n[..], false);
            let encoded = C::ext_node(&enc_nibble[..], v_hash); // TODO try rem clone
            cb_ext(encoded, true);
          }
        } else {
          let v_hash = node.hash(); // TODO proper match!!
          if d > 0 {
            let nibble: u8 = nibble_at(&ref_branch.as_ref()[..],d-1);
            // TODO capacity vec of 64?
            self.set_node(d-1, nibble as usize, CacheNode::Ext(vec![unit as u8], v_hash));
          } else {
            let enc_nibble = encoded_nibble(&[unit as u8], false);
            let encoded = C::ext_node(&enc_nibble[..], v_hash); // TODO try rem clone
            cb_ext(encoded, true);
          }
        }
      } else {
        let encoded = self.encode_branch(d, has_val, cb_ext);
        self.reset_depth(d);
        let hash = cb_ext(encoded, d == 0);
        // clear tmp val
        // put hash in parent
        if d > 0 {
          let nibble: u8 = nibble_at(&ref_branch.as_ref()[..],d-1);
          self.set_node(d-1, nibble as usize, CacheNode::Hash(hash));
        } else {
          // reachable !!
        }
      }
    }
  }
}

// TODO try split struct
enum CacheNode<HO> {
  None,
  Hash(ChildReference<HO>),
  Ext(Vec<u8>,ChildReference<HO>),// vec<u8> for nibble slice is not super good looking): TODO bench diff if explicitely boxed
}

impl<HO: Clone> Clone for CacheNode<HO> {
  fn clone(&self) -> Self {
    match self {
      CacheNode::None => CacheNode::None,
      CacheNode::Hash(ChildReference::Hash(ref h)) => CacheNode::Hash(ChildReference::Hash(h.clone())),
      CacheNode::Hash(ChildReference::Inline(ref h, s)) => CacheNode::Hash(ChildReference::Inline(h.clone(), *s)),
      CacheNode::Ext(ref v, ChildReference::Hash(ref h)) => CacheNode::Ext(v.clone(), ChildReference::Hash(h.clone())),
      CacheNode::Ext(ref v, ChildReference::Inline(ref h, s)) => CacheNode::Ext(v.clone(), ChildReference::Inline(h.clone(), *s)),
    }
  }
}

fn clone_child_ref<HO: Clone>(r: &ChildReference<HO>) -> ChildReference<HO> {
  match r {
    ChildReference::Hash(ref h) => ChildReference::Hash(h.clone()),
    ChildReference::Inline(ref h, s) => ChildReference::Inline(h.clone(), *s),
  }
}

impl<HO> CacheNode<HO> {
  // unsafe accessors TODO bench diff with safe one
  fn hash(self) -> ChildReference<HO> {
    if let CacheNode::Hash(h) = self {
      return h
    }
    unreachable!()
  }
  fn ext(self) -> (Vec<u8>,ChildReference<HO>) {
    if let CacheNode::Ext(n,h) = self {
      return (n,h)
    }
    unreachable!()
  }
}

pub fn trie_visit<H, C, I, A, B, F>(input: I, cb_ext: &mut F) 
  where
    I: IntoIterator<Item = (A, B)>,
    A: AsRef<[u8]> + Ord,
    B: AsRef<[u8]>,
    H: Hasher,
    C: NodeCodec<H>,
    F: FnMut(Vec<u8>, bool) -> ChildReference<H::Out>
  {
  let mut depth_queue = CacheAccum::<H,C,B>::new();
  // compare iter ordering
  let mut iter_input = input.into_iter();
  if let Some(mut prev_val) = iter_input.next() {
    // depth of last item TODO rename to last_depth
    let mut prev_depth = 0;

    for (k, v) in iter_input {
      let common_depth = biggest_depth(&prev_val.0.as_ref()[..], &k.as_ref()[..]);
      // 0 is a reserved value : could use option
      let depth_item = common_depth + 1;
      if common_depth == prev_val.0.as_ref().len() * 2 {
        // the new key include the previous one : branch value case
        depth_queue.1[common_depth] = Some(prev_val.1);
      } else if depth_item >= prev_depth {
        // put prev with next
        depth_queue.flush_val(cb_ext, depth_item, &prev_val);
      } else if depth_item < prev_depth {
        // do not put with next
        depth_queue.flush_val(cb_ext, prev_depth, &prev_val);
        let ref_branches = prev_val.0;
        depth_queue.flush_branch(cb_ext, ref_branches, depth_item, prev_depth);
      }

      prev_val = (k, v);
      prev_depth = depth_item;
    }
    // last pendings
    if prev_depth == 0 {
      // one element
      let (ref k2,ref v2) = &prev_val; 
      let nkey = NibbleSlice::new_offset(&k2.as_ref()[..],prev_depth).encoded(true);
      let encoded = C::leaf_node(&nkey.as_ref()[..], &v2.as_ref()[..]);
      cb_ext(encoded, true);
    } else {
      depth_queue.flush_val(cb_ext, prev_depth, &prev_val);
      let ref_branches = prev_val.0;

      depth_queue.flush_branch(cb_ext, ref_branches, 0, prev_depth);
    }
  } else {
    // nothing null root case
    cb_ext(C::empty_node(), true);
  }
}

#[macro_export]
/// fn mut to feed a hash map with trie elements
macro_rules! trie_db_builder {
	($memdb: ident, $root_dest: ident) => {
    |enc_ext: Vec<u8>, is_root: bool| {
      if !is_root && enc_ext.len() < DEPTH/2 {
        let l = enc_ext.len();
        return ChildReference::Inline(enc_ext[..].into(), l);
      }
      let hash = $memdb.insert(&enc_ext[..]);
      if is_root {
        $root_dest = hash.clone();
      };
      ChildReference::Hash(hash)
    };
	}
}

#[macro_export]
/// fn mut to feed a hash map with trie elements
macro_rules! trie_root_only {
	($hash_trait: ident, $root_dest: ident) => {
    |enc_ext: Vec<u8>, is_root: bool| {
      if !is_root && enc_ext.len() < DEPTH/2 {
        let l = enc_ext.len();
        return ChildReference::Inline(enc_ext[..].into(), l);
      }
      let hash = $hash_trait::hash(&enc_ext[..]);
      if is_root {
        $root_dest = hash.clone();
      };
      ChildReference::Hash(hash)
    };
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
    let mut cb = trie_db_builder!(hashdb, root_new);
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
  compare_impl(vec![])
}

#[test]
fn trie_one_node () {
  compare_impl(vec![
    (vec![1u8,2u8,3u8,4u8],vec![7u8]),
  ]);
}

#[test]
fn root_extension () {
  compare_impl(vec![
    (vec![1u8,2u8,3u8,3u8],vec![8u8;32]),
    (vec![1u8,2u8,3u8,4u8],vec![7u8;32]),
  ]);
}

#[test]
fn root_extension_bis () {
  compare_root(vec![
    (vec![1u8,2u8,3u8,3u8],vec![8u8;32]),
    (vec![1u8,2u8,3u8,4u8],vec![7u8;32]),
  ]);
}



#[cfg(test)]
fn compare_impl(data: Vec<(Vec<u8>,Vec<u8>)>) {
  let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut hashdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let mut root_new = H256::new();
  {
    let mut cb = trie_db_builder!(hashdb, root_new);
    trie_visit::<KeccakHasher, RlpCodec, _, _, _, _>(data.clone().into_iter(), &mut cb);
  }
  let root = {
    let mut root = H256::new();
    let mut t = TrieDBMut::new(&mut memdb, &mut root);
    for i in 0..data.len() {
      t.insert(&data[i].0[..],&data[i].1[..]);
    }
    let mut nbelt = 0;
    t.root().clone()
  };
  {
    let t = TrieDB::new(&memdb, &root).unwrap();
    println!("{:?}", t);
    for a in t.iter().unwrap() {
      println!("a:{:?}", a);
    }
  }
  {
    let t = TrieDB::new(&hashdb, &root_new).unwrap();
    println!("{:?}", t);
    for a in t.iter().unwrap() {
      println!("a:{:?}", a);
    }
  }

  assert_eq!(root, root_new);
}

#[cfg(test)]
fn compare_root(data: Vec<(Vec<u8>,Vec<u8>)>) {
  let mut root_new = H256::new();
  {
    let mut cb = trie_root_only!(KeccakHasher, root_new);
    trie_visit::<KeccakHasher, RlpCodec, _, _, _, _>(data.clone().into_iter(), &mut cb);
  }
  let mut memdb = MemoryDB::<KeccakHasher, DBValue>::new();
  let root = {
    let mut root = H256::new();
    let mut t = TrieDBMut::new(&mut memdb, &mut root);
    for i in 0..data.len() {
      t.insert(&data[i].0[..],&data[i].1[..]);
    }
    let mut nbelt = 0;
    t.root().clone()
  };

  assert_eq!(root, root_new);
}

#[test]
fn trie_middle_node () {
  compare_impl(vec![
    (vec![1u8,2u8],vec![8u8;32]),
    (vec![1u8,2u8,3u8,4u8],vec![7u8;32]),
  ]);
}

#[test]
fn trie_middle_node2 () {
  compare_impl(vec![
    (vec![0u8,2u8,3u8,5u8,3u8],vec![1u8;32]),
    (vec![1u8,2u8],vec![8u8;32]),
    (vec![1u8,2u8,3u8,4u8],vec![7u8;32]),
    (vec![1u8,2u8,3u8,5u8],vec![7u8;32]),
    (vec![1u8,2u8,3u8,5u8,3u8],vec![7u8;32]),
  ]);
}

#[test]
fn trie_middle_node2x () {
  compare_impl(vec![
    (vec![0u8,2u8,3u8,5u8,3u8],vec![1u8;2]),
    (vec![1u8,2u8],vec![8u8;2]),
    (vec![1u8,2u8,3u8,4u8],vec![7u8;2]),
    (vec![1u8,2u8,3u8,5u8],vec![7u8;2]),
    (vec![1u8,2u8,3u8,5u8,3u8],vec![7u8;2]),
  ]);
}

/*

found a leaf 2, depth 1
k [1, 2, 3, 4]
found a leaf 2, depth 1
k [1, 2]
t1-0
ti0
TrieDB { hash_count: 0, root: Node::Extension { slice: 0'1'0'2, item: Node::Branch { nodes: [Node::Leaf { slice: 3'0'4, value: [7] }, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty,
 Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty], value: Some([8]) } } }
a:Ok(([1, 2], [8]))
a:Ok(([1, 2, 3, 4], [7]))
TrieDB { hash_count: 0, root: Node::Branch { nodes: [Node::Leaf { slice: 1'0'2, value: [8] }, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty,
Node::Empty, Node::Empty, Node::Empty, Node::Empty], value: None } }
a:Ok(([1, 2], [8]))

found a leaf 2, depth 1
k [1, 2]
found a leaf 2, depth 1
k [1, 2, 3, 4]
t1-0
ti0
TrieDB { hash_count: 0, root: Node::Extension { slice: 0'1'0'2, item: Node::Branch { nodes: [Node::Leaf { slice: 3'0'4, value: [7] }, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty,
 Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty], value: Some([8]) } } }
a:Ok(([1, 2], [8]))
a:Ok(([1, 2, 3, 4], [7]))
TrieDB { hash_count: 0, root: Node::Branch { nodes: [Node::Leaf { slice: 1'0'2'0'3'0'4, value: [7] }, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty, Node:
:Empty, Node::Empty, Node::Empty, Node::Empty, Node::Empty], value: None } }
a:Ok(([1, 2, 3, 4], [7]))

 */
