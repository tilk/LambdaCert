var o = {a:1,f:function(){return this.a}};
with(o) { f() }
