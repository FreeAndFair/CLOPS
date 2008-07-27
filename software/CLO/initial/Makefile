.PHONY: doc build celan run



build:
	javac -Xlint -d bin java/*.java

clean:
	rm -rf bin/*
	rm -rf doc/*

run: build
	java -ea -cp bin Main -1 -l -c -u -x -c


jml:
	jml java/*.java

doc:
	javadoc -d doc java/*.java
