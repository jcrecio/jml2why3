prove:
	cd src && why3 prove  -P alt-ergo -L . algo1.mlw

.PHONY: extract

extract:
	cd src && why3 extract -L . -D ocaml64 --recursive algo1.mlw -o algo1.ml
	ocamlfind ocamlopt -package zarith -c -i src/algo1.ml

test:
	make -C jml2why3 test
