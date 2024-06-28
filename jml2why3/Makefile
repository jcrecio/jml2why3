OPENJMLVERSION=v0.3
OPENJMLJAR=openjml-$(OPENJMLVERSION).jar
CLASSPATH ?=

.PHONY: all replay-proofs openjml.jar

build:
	dune build @install
	ln -sf _build/install/default/bin .

all: build replay-proofs test

replay-proofs: examples/GroupeClassement-generated.mlw examples/GroupeClassement__permutation-generated.mlw
	why3 replay jml2why3
	why3 replay -L . examples/groupe_classement_permutation
	why3 replay -L . examples/groupe_classement_permutation_i32
	why3 replay -L . examples/GroupeClassement-generated
	why3 replay -L . examples/GroupeClassement__permutation-generated

clean:
	dune clean
	rm -f bin

openjml.jar: $(OPENJMLJAR)

$(OPENJMLJAR):
	wget -O $@ https://github.com/benozol/OpenJML/releases/download/$(OPENJMLVERSION)/openjml.jar

%.java.json: $(OPENJMLJAR) %.java
	java -cp $(CLASSPATH) -jar $< -command=tojson $*.java

%-generated.mlw: %.java.json build
	./bin/jml2why3 --dont-prove --write-mlw $@ $<

# test: examples/GroupeClassement.java.json build
# 	./bin/jml2why3 --write-mlw examples/GroupeClassement-generated.mlw $<

test: replay-proofs
	make -C report

# make examples/GroupeClassementPermutation-generated.mlw
# why3 replay examples/GroupeClassementPermutation-generated
