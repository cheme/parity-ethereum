cargo build --release --target wasm32-unknown-unknown 
ln -s ../../target
wasm-pack build  --target browser
rm  ./target
cd pkg
npx webpack
cd dist

