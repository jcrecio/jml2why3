OPENJMLVERSION=v0.3
ESC=java -jar openjml-v0.3.jar -command=esc -progress -trace -subexpressions -verboseness=2

test:
	$(ESC) GroupeClassement__everything_arrays.java
	$(ESC) GroupeClassement__array_queue.java

openjml.jar: openjml-$(OPENJMLVERSION).jar

openjml-$(OPENJMLVERSION).jar:
	wget -O $@ https://github.com/benozol/OpenJML/releases/download/$(OPENJMLVERSION)/openjml.jar
