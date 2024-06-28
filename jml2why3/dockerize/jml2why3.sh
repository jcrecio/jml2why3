FILES_TO_INCLUDE_PATH = $2
M2_REPO_PATH = $3

if [ "$1" == "build" ]; then
    docker build -t jml2why3 .
elif [ "$1" == "run" ]; then
    docker run -it -v "$FILES_TO_INCLUDE_PATH":/files -v "$M2_REPO_PATH":/root/.m2 --name jml2why3 jml2why3
else
    echo "Command not recognised: $1"
    echo "----------------------"
    echo "Use build or run":
    echo "1. build: will create the docker image that contains jml2why3"
    echo "2. run: run the previously created docker image as a container"
fi