"use strict";
Number.prototype.f = function () { return typeof this };
var x = 1;
var y = new Number(2);
x.f()+y.f()
