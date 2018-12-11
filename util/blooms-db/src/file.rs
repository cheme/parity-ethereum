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

use std::io::{Seek, SeekFrom, Write, Read};
#[cfg(feature = "in-memory")]
use std::io::Cursor;
use std::path::Path;
use std::{io, fs};

use ethbloom;
#[cfg(not(feature = "in-memory"))]
/// Autoresizable file containing blooms.
pub struct File {
	/// Backing file.
	file: fs::File,
	/// Current file len.
	len: u64,
}

#[cfg(feature = "in-memory")]
/// Autoresizable file containing blooms.
pub struct File {
	/// Backing file : TODO if in memory is good makes write in backing file
	file: fs::File,
  /// Super dirty
  mem: Cursor<Vec<u8>>,
	/// Current file len.
	len: u64,
}



#[cfg(not(feature = "in-memory"))]
impl File {
	/// Opens database file. Creates new file if database file does not exist.
	pub fn open<P>(path: P) -> io::Result<File> where P: AsRef<Path> {
		let file = fs::OpenOptions::new()
			.read(true)
			.write(true)
			.create(true)
			// appending is done manually by calling `ensure_space_for_write`
			.append(false)
			.open(path)?;
		let len = file.metadata()?.len();

		let file = File {
			file,
			len,
		};

		Ok(file)

	}

	/// Resizes the file if there is not enough space to write bloom at given position.
	fn ensure_space_for_write(&mut self, pos: u64) -> io::Result<()> {
		// position to write + 256 bytes
		let required_space = (pos + 1) * 256;
		if required_space > self.len {
			self.file.set_len(required_space)?;
			self.len = required_space;
		}
		Ok(())
	}

	/// Read bloom at given position.
	pub fn read_bloom(&self, pos: u64) -> io::Result<ethbloom::Bloom> {
		let mut file_ref = &self.file;
		file_ref.seek(SeekFrom::Start(pos * 256))?;
		let mut bloom = ethbloom::Bloom::default();
		file_ref.read_exact(&mut bloom)?;
		Ok(bloom)
	}

	/// Accrue bloom into bloom at given position.
	pub fn accrue_bloom<'a, B>(&mut self, pos: u64, bloom: B) -> io::Result<()> where ethbloom::BloomRef<'a>: From<B> {
		self.ensure_space_for_write(pos)?;
		let mut old_bloom: ethbloom::Bloom = self.read_bloom(pos)?;
		old_bloom.accrue_bloom(bloom);
		let mut file_ref = &self.file;
		file_ref.seek(SeekFrom::Start(pos * 256))?;
		file_ref.write_all(&old_bloom)
	}

	/// Replace bloom at given position with a new one.
	pub fn replace_bloom<'a, B>(&mut self, pos: u64, bloom: B) -> io::Result<()> where ethbloom::BloomRef<'a>: From<B> {
		self.ensure_space_for_write(pos)?;
		let mut file_ref = &self.file;
		file_ref.seek(SeekFrom::Start(pos * 256))?;
		file_ref.write_all(ethbloom::BloomRef::from(bloom).data())
	}

	/// Returns an iterator over file.
	///
	/// This function needs to be mutable `fs::File` is just a shared reference a system file handle.
	/// https://users.rust-lang.org/t/how-to-handle-match-with-irrelevant-ok--/6291/15
	pub fn iterator_from(&mut self, pos: u64) -> io::Result<FileIterator> {
		let mut buf_reader = io::BufReader::new(&self.file);
		buf_reader.seek(SeekFrom::Start(pos * 256))?;

		let iter = FileIterator {
			file: buf_reader,
		};

		Ok(iter)
	}

	/// Flush outstanding modifications to the disk
	pub fn flush(&mut self) -> io::Result<()> {
		self.file.flush()
	}
}

#[cfg(feature = "in-memory")]
impl File {
	/// Opens database file. Creates new file if database file does not exist.
	pub fn open<P>(path: P) -> io::Result<File> where P: AsRef<Path> {
		let mut file = fs::OpenOptions::new()
			.read(true)
			.write(true)
			.create(true)
			// appending is done manually by calling `ensure_space_for_write`
			.append(false)
			.open(path)?;
		let len = file.metadata()?.len();

    let mut mem = Vec::with_capacity(len as usize);
    file.read_to_end(&mut mem)?;
    let mem = Cursor::new(mem);
		let file = File {
			file,
			len,
      mem,
		};
    

		Ok(file)

	}

	/// Resizes the file if there is not enough space to write bloom at given position.
	fn ensure_space_for_write(&mut self, pos: u64) -> io::Result<()> {
		let required_space = (pos + 1) * 256;
		if required_space > self.len {
			//self.file.set_len(required_space)?;
      self.mem.get_mut().extend_from_slice(&vec![0;(required_space - self.len) as usize][..]);
			self.len = required_space;
		}
		Ok(())
	}

	/// Read bloom at given position.
	pub fn read_bloom(&self, pos: u64) -> io::Result<ethbloom::Bloom> {
		let mut file_ref = Cursor::new(self.mem.get_ref());
		file_ref.seek(SeekFrom::Start(pos * 256))?;
		let mut bloom = ethbloom::Bloom::default();
		file_ref.read_exact(&mut bloom)?;
		Ok(bloom)
	}

	/// Accrue bloom into bloom at given position.
	pub fn accrue_bloom<'a, B>(&mut self, pos: u64, bloom: B) -> io::Result<()> where ethbloom::BloomRef<'a>: From<B> {
		self.ensure_space_for_write(pos)?;
		let mut old_bloom: ethbloom::Bloom = self.read_bloom(pos)?;
		old_bloom.accrue_bloom(bloom);
		let mut file_ref = &mut self.mem;
		file_ref.seek(SeekFrom::Start(pos * 256))?;
		file_ref.write_all(&old_bloom)
	}

	/// Replace bloom at given position with a new one.
	pub fn replace_bloom<'a, B>(&mut self, pos: u64, bloom: B) -> io::Result<()> where ethbloom::BloomRef<'a>: From<B> {
		self.ensure_space_for_write(pos)?;
		let mut file_ref = &mut self.mem;
		file_ref.seek(SeekFrom::Start(pos * 256))?;
		file_ref.write_all(ethbloom::BloomRef::from(bloom).data())
	}

#[cfg(not(feature = "in-memory"))]
	/// Returns an iterator over file.
	///
	/// This function needs to be mutable `fs::File` is just a shared reference a system file handle.
	/// https://users.rust-lang.org/t/how-to-handle-match-with-irrelevant-ok--/6291/15
	pub fn iterator_from(&mut self, pos: u64) -> io::Result<FileIterator> {
		let mut buf_reader = io::BufReader::new(&self.mem);
		buf_reader.seek(SeekFrom::Start(pos * 256))?;

		let iter = FileIterator {
			file: buf_reader,
		};

		Ok(iter)
	}
#[cfg(feature = "in-memory")]
	/// Returns an iterator over file.
	///
	/// This function needs to be mutable `fs::File` is just a shared reference a system file handle.
	/// https://users.rust-lang.org/t/how-to-handle-match-with-irrelevant-ok--/6291/15
	pub fn iterator_from(&mut self, pos: u64) -> io::Result<FileIterator> {
		let mut buf_reader = &mut self.mem;
		buf_reader.seek(SeekFrom::Start(pos * 256))?;

		let iter = FileIterator {
			file: buf_reader,
		};

		Ok(iter)
	}


	/// Flush outstanding modifications to the disk
	pub fn flush(&mut self) -> io::Result<()> {
    // TODO flush every n flush??
		Ok(())
	}
}

#[cfg(feature = "in-memory")]
impl Drop for File {
  fn drop(&mut self) {
		self.file.seek(SeekFrom::Start(0)).unwrap();
    self.file.write_all(&self.mem.get_ref()[..]).unwrap();
    self.file.set_len(self.mem.get_ref().len() as u64).unwrap();
  }
}

#[cfg(feature = "in-memory")]
/// Iterator over blooms of a single file.
pub struct FileIterator<'a> {
	/// Backing file.
	file: &'a mut Cursor<Vec<u8>>,
}


#[cfg(not(feature = "in-memory"))]
/// Iterator over blooms of a single file.
pub struct FileIterator<'a> {
	/// Backing file.
	file: io::BufReader<&'a fs::File>,
}

impl<'a> FileIterator<'a> {
	/// Advance file by n blooms
	pub fn advance(&mut self, n: u64) -> io::Result<()> {
		self.file.seek(SeekFrom::Current(n as i64 * 256))?;
		Ok(())
	}
}

impl<'a> Iterator for FileIterator<'a> {
	type Item = io::Result<ethbloom::Bloom>;

	fn next(&mut self) -> Option<Self::Item> {
		let mut bloom = ethbloom::Bloom::default();
		match self.file.read_exact(&mut bloom) {
			Ok(_) => Some(Ok(bloom)),
			Err(ref err) if err.kind() == io::ErrorKind::UnexpectedEof => None,
			Err(err) => Some(Err(err)),
		}
	}
}

#[cfg(test)]
mod tests {
	use ethbloom::Bloom;
	use tempdir::TempDir;
	use super::File;

	#[test]
	fn test_file() {
		let tempdir = TempDir::new("").unwrap();
		let mut file = File::open(tempdir.path().join("file")).unwrap();
		file.accrue_bloom(0, &Bloom::from(1)).unwrap();
		file.flush().unwrap();
		assert_eq!(file.read_bloom(0).unwrap(), Bloom::from(1));

	}
}
