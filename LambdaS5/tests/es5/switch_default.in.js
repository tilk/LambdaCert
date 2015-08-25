function f(x) { print(x); return x }
function t(y) {
    print("test "+y);
    switch(y) {
	case f(0): print("run0")
	case f(1): print("run1")
	default: print("deflt")
	case f(2): print("run2")
	case f(3): print("run3")
    }
}
t(0);
t(1);
t(2);
t(3);
t(4)
