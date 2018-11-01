#cargo build --target wasm32-unknown-unknown 
ln -s ../target
wasm-pack build --target browser
sed -i '/function getUint8Memory/ c\export function getUint8Memory() {' ./pkg/evmbin.js
rm  ./target
cd pkg
npx webpack
cd dist

