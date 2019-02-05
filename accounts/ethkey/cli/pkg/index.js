const js = import("./ethkey_cli.js");

js.then(js => {
  window.tested_wasm = js;
  js.ethkey(["generate", "random"]);
  js.ethkey(["generate", "prefix", "ab"]);
  let skey = js.ethkey(["generate", "random", "-s"]);
  console.log("skey : " + skey);
  // message length to skey length only
  let msign = js.ethkey(["sign", skey, skey]);
  console.log("msign : " + msign);
  let pubk = js.ethkey(["info", skey, "-p"]);
  console.log("pubk : " + pubk);
  let addr = js.ethkey(["info", skey, "-a"]);
  console.log("addr : " + addr);
  js.ethkey(["verify", "public", pubk, msign, skey]);
  console.log("after verify public");
  js.ethkey(["verify", "address", addr, msign, skey]);
  console.log("after verify address");

 
});
