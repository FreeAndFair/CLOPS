.PHONY: doc build clean run

build:
	javac -Xlint -d bin java/*.java

clean:
	rm -rf bin/*
	rm -rf doc/*

run: build
	java -ea -cp bin Main -1 -l -c -u -x -c


jml:
	jml -G java/*.java

doc:
	javadoc -d doc java/*.java
