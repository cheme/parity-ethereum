#cargo build --target wasm32-unknown-unknown --no-default-features
ln -s ../target
wasm-pack build --target browser #-- --no-default-features
sed -i '/function getUint8Memory/ c\export function getUint8Memory() {' ./pkg/evmbin.js
rm ./target
cd pkg
cp -rf ./env ./node_modules/
cp ./package.json_ok ./package.json
#npm install
npx webpack
cd dist

