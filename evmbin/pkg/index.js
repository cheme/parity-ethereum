
import env from "./env.js";

const js = import("./evmbin.js");

js.then(js => {
  window.tested_wasm = js;

 
});
