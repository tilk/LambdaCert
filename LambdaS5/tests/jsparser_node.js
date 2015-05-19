var fs = require('fs');
var esprima = require('esprima');
fs.readFile(process.argv[2], 'utf8', function (err,data) {
	if (err) { return console.log(err) }
	console.log(JSON.stringify(esprima.parse(data)))
});
