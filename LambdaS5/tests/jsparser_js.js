load('esprima.js');
print(JSON.stringify(esprima.parse(read(arguments[1],{loc:true}))))
