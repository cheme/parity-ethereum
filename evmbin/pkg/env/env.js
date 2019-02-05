

export function malloc_usable_size(ptr) {
	// disable all heapsize related features for he wasm build
 return 0;
}

//#[wasm_bindgen(catch)]
//fn open_browserfs(path: &str) -> Result<JsFile, JsValue>;
export function open_browserfs(path, flag) {
	let fd = window.fs.openSync(path, flag);
	return { fd: fd, cursor: 0 };
}


//#[wasm_bindgen(catch)]
//fn read_browserfs(jsfile: &JsFile, buff: *mut u8, len: u32) -> Result<u32, JsValue>;
export function read_browserfs(file, ptr, len) {
	let mem_buf = window.tested_wasm.getUint8Memory();
	let nbread = window.fs.readSync(file.fd,mem_buf,ptr,len,file.cursor);

	file.cursor += nbread;
	return nbread;
}

//fn close_browserfs(jsfile: &JsFile);
export function close_browserfs(file) {
	window.fs.closeSync(file.fd);
}




//#[wasm_bindgen(catch)]
//fn write_browserfs(jsfile: &JsFile, buff: *const u8, len: u32) -> Result<u32, JsValue>;
export function write_browserfs(file, ptr, len) {
	let mem_buf = window.tested_wasm.getUint8Memory();
	let nbwrite = window.fs.writeSync(file.fd,mem_buf,ptr,len,file.cursor);

	file.cursor += nbwrite;
	return nbwrite;
}


//#[wasm_bindgen(catch)]
//fn flush_write_browserfs(jsfile: &JsFile) -> Result<(), JsValue>;
export function flush_write_browserfs(file) {
	fs.fsyncSync(file.fd);
}



//#[wasm_bindgen(catch)]
//fn seek_browserfs(jsfile: &JsFile, mov: i64) -> Result<u32, JsValue>;
export function seek_browserfs(file, mov) {
	let npos = file.cursor + mov;
	if (npos < 0) {
		throw "Cannot seek file before start";
	}
	file.cursor = npos;
	return file.cursor;
}

//fn seek_browserfs_from_start(jsfile: &JsFile, mov: u32) -> u32;
export function seek_browserfs_from_start(file, mov) {
	file.cursor = mov;
	return file.cursor;
}

//#[wasm_bindgen(catch)]
//fn seek_browserfs_from_end(jsfile: &JsFile, mov: i64) -> Result<u32, JsValue>;
// warn unused and untested
export function seek_browserfs_from_end(file, mov) {
	let stat = fs.fstatSync;
	let npos = stat.size + mov;
	if (npos < 0) {
		throw "Cannot seek file of size " + stat.size + " before start";
	}
	file.cursor = npos;
	return file.cursor;
}

//#[wasm_bindgen(catch)]
//fn set_len_browserfs(len: u64) -> Result<(), JsValue>;
export function set_len_browserfs(file, len) {
	fs.truncateSync(file.path);
}


//fn len_browserfs(jsfile: &JsFile) -> u64;
export function len_browserfs(file) {
	let stat = fs.fstatSync(file.fd, { bigint: true });
  // at this time no bigint support from memfs TODO maybe simply switch to 32
	return BigInt(stat.size);
}


