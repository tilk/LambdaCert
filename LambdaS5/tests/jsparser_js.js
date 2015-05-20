load('esprima.js');
var text = read(arguments[1],{loc:true});
try {
    var ast = esprima.parse(text)
} catch(e) {
    print(JSON.stringify({type:"ParseError", message:e.message}));
    quit(1);
}
print(JSON.stringify(ast))
