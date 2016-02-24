load('esprima.js');
var text = read(scriptArgs[1]);
try {
    var ast = esprima.parse(text)
} catch(e) {
    print(JSON.stringify({type:"ParseError", message:e.message}));
    quit(1);
}
print(JSON.stringify(ast))
