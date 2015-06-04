
all: configure coq interpreter snapshot

doc: configure
	make -C coq/ gallinahtml

configure: coq/configure coq/*.v
	cd coq;	./configure

coq: configure
	make -C coq/ LjsExtraction.vo # to omit metatheory

coq-all: configure
	make -C coq/ 

copy_ljs:
	mkdir -p build/
	cp caml/ljs/ljs_lexer.mll caml/ljs/ljs_parser.mly caml/ljs/*.ml build/

copy: coq caml/ copy_ljs
	mkdir -p build/
	cp coq/*.ml coq/*.mli build/
	cp caml/*.ml caml/*.mli caml/_tags build/

build/eval.p.native: copy
	cd build/; ocamlbuild -use-ocamlfind eval.p.native

profiling: build/eval.p.native

build/eval.native: copy
	cd build/; ocamlbuild -use-ocamlfind eval.native

native: build/eval.native 

build/eval.byte: copy
	cd build/; ocamlbuild -use-ocamlfind eval.byte -tag debug

byte: build/eval.byte 

interpreter: native

tests/es5.dump: envs/es5.env build/eval.native
	./build/eval.native -env envs/es5.env -save tests/es5.dump

snapshot: tests/es5.dump

tests: snapshot
	tests/run_tests.py tests/es5.dump

quicktests:
	tests/run_tests.py

#coq/LjsInitEnv.v: build/eval.native tests/es5.dump
#	./build/eval.native -load tests/es5.dump -coq-save coq/LjsInitEnv.v

initenv: tests/es5.dump
	./build/eval.native -load tests/es5.dump -coq-save coq/LjsInitEnv.v

clean:
	make -C coq/ clean
	rm -f coq/*.ml coq/*.mli
	rm -rf build/*

.PHONY: coq caml clean tests
