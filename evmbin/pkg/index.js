
const js = import("./evmbin.js");
import atest from '../../ethcore/res/ethereum/tests/VMTests/vmTests/suicide.json';
import stest from '../../ethcore/res/ethereum/tests/GeneralStateTests/stCreate2/create2InitCodes.json';

import fs from 'memfs';

window.fs = fs;

js.then(js => {
	window.tested_wasm = js;
	//fs.mkdtempSync('/temp');
	fs.mkdirSync('/temp');
	fs.mkdirSync('/home');
	fs.mkdirSync('/VMTests');
	fs.mkdirSync('/VMTests/vmTests');
	fs.writeFileSync('/VMTests/vmTests/suicide.json', JSON.stringify(atest));
	window.jsonread = fs.readFileSync('/VMTests/vmTests/suicide.json', 'utf8');
	js.evmbin(["stats-jsontests-vm","/VMTests/vmTests/suicide.json"]);

	fs.mkdirSync('/GeneralStateTests');
	fs.mkdirSync('/GeneralStateTests/stCreate2');
	fs.writeFileSync('/GeneralStateTests/stCreate2/create2InitCodes.json', JSON.stringify(stest));
	js.evmbin(["state-test", '/GeneralStateTests/stCreate2/create2InitCodes.json']);
	js.evmbin(["state-test", "--json", '/GeneralStateTests/stCreate2/create2InitCodes.json']);
  // std-json currently do not work (probably not compatible with the way we display to console with wasm
	//js.evmbin(["state-test", "--std-json", '/GeneralStateTests/stCreate2/create2InitCodes.json']);
 
	// some of evm_import menu from './portal/content/json/menu.json';jsontestss_bench.sh
	// No support currently for directory TODO check if could loop on github project instead
/*	js.evmbin(["stats-jsontests-vm", "/VMTests/vmArithmeticTest"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmBitwiseLogicOperation"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmBlockInfoTest"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmEnvironmentalInfo"]);
	//js.evmbin(["stats-jsontests-vm", "/VMTests/vmIOandFlowOperations"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmLogTest"]);
	//js.evmbin(["stats-jsontests-vm", "/VMTests/vmPerformance"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmPushDupSwapTest"]);
	//js.evmbin(["stats-jsontests-vm", "/VMTests/vmRandomTest"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmSha3Test"]);
	//js.evmbin(["stats-jsontests-vm", "/VMTests/vmSystemOperations"]);
	js.evmbin(["stats-jsontests-vm", "/VMTests/vmTests"]);*/
	// scripts/evm_uint_bench.sh
	let code1 = "606060405260005b620f42408112156019575b6001016007565b600081905550600680602b6000396000f3606060405200";
	js.evmbin(["stats", "--code", code1, "--gas", "4402000"]);
	console.log("^^^^ usize");
/*	js.evmbin(["stats", "--code", code1]);
	console.log("^^^^ U256");
	let code2 = "6060604052600360056007600b60005b620f4240811215607f5767ffe7649d5eca84179490940267f47ed85c4b9a6379019367f8e5dd9a5c994bba9390930267f91d87e4b8b74e55019267ff97f6f3b29cda529290920267f393ada8dd75c938019167fe8d437c45bb3735830267f47d9a7b5428ffec019150600101600f565b838518831882186000555050505050600680609a6000396000f3606060405200";
	js.evmbin(["stats", "--code", code2, "--gas", "143020115"]);
	console.log("^^^^ usize");
	js.evmbin(["stats", "--code", code2]);
	console.log("^^^^ U256");*/
});
