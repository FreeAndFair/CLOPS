CLASSPTH := ./bin

JAVA := java -ea -classpath ${CLASSPTH}

build: bin
	export FILES=`find "./src/java/" -name "*.java"` ;\
	javac  -Xlint:all -d bin -classpath "./src/java" $$FILES

bin:
	mkdir bin

javadoc:
	mkdir javadoc

doc: javadoc
	export FILES=`find "./src/java/" -name "*.java"` ;\
	javadoc -d "./javadoc" -classpath ${CLASSPTH} $${FILES} 

clean:
	rm -rf bin/*
