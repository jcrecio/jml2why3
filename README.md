# jml2why3 as a docker image
This repository is a copy of an Inria repository [code source Java](https://framagit.org/parcoursup/algorithmes-de-parcoursup) slightly modified to use the tool jml2why as a docker image.

We created a copy of the repository that contains the tool jml2why3 from Inria to automate the process to install the tool in a clean environment.

We can pull the image from docker hub or recreate it ourselves.

1. Recreate the image:

    It can be cloned from https://github.com/jcrecio/jml2why3
There is an added folder inside jml2why3 called dockerize. Run ```bash dockerize/jml2why3.sh build```

2. Pull the image: ```docker pull jcrecio/jml2why3 ```

Now let´s run the image so we can start using the jml2why3 tool:
```
bash dockerize/jml2why3.sh run <path to mount of volume to interact with projects> <.m2 local path>
```
After running the container, we will be connected internally to its bash, activate the environment inside to run the tool:
```
opam switch 4.08.0
eval $(opam env)
cd jml2why3root/jml2why3
make
make openjml-v0.3.jar
```

Now, we can run the tool, for instance, to generate the typed AST for a java file:
```
export TOJSON_CLASSPATH=<classpath to make the java file be compilable and runnable>
make <javafile.java>.json
```

We modified the jml2why3 Makefile to able to pass the classpath to the openjml command to generate the typed AST:

```
# Line 28 of jml2why3/Makefile

%.java.json: $(OPENJMLJAR) %.java
	java -jar $< -cp $(TOJSON_CLASSPATH) -command=tojson $*.java
```