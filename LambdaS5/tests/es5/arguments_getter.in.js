var x = {get x() { return arguments.length }, set y(v) { return arguments.length }};
print(x.x)
print(x.y = 0)
